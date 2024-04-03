{-# LANGUAGE NoRebindableSyntax  #-}
{-# OPTIONS_GHC -fplugin=IfSat.Plugin #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-|
Module      : Blarney.Core.Retime
Description : Time Transformation from Lava

This module provides the time transformation from Lava.
This transformation allows computing several cycles of a circuit in a single
cycle.
-}
module Blarney.Core.Retime (unroll, unroll') where

import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import qualified Blarney.Core.Vactor as V

-- Utils
import Blarney.Core.Prim
import Blarney.Core.Utils

-- IfSat
import Data.Constraint.If

-- Standard imports
import Prelude
import Data.Proxy
import GHC.TypeLits
import GHC.Generics

import Data.List
  ( transpose
  , singleton
  )
import Data.Function (fix)

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- This transformation allows computing several cycles of a circuit in a single
-- cycle
-- The compression ratio is determined by the size of the input list
-- cf Lava's timeTransform

unroll :: (Bits a, Bits b, KnownNat (SizeOf a)) => (a -> b) -> ([a] -> [b])
unroll circ [] = []
unroll circ inps@(inp:_) =
    map (unpack . FromBV)
  . (IntMap.! rootID)
  . fix
  $ aux rootBV IntSet.empty
 where
  n = length inps
  symb = "#retime#"
  rootBV = toBV . pack . circ . unpack $ inputPin symb
  rootID = bvInstId rootBV

  aux :: BV -> IntSet -> IntMap [BV] -> IntMap [BV]
  aux bv iset imap =
    if id `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton id (
          case bv of
            BV{bvPrim=(Input w s)} | s == symb -> map (toBV . pack) inps
            BV{bvPrim=(Register initVal w), bvInputs=[regIn], bvOutput=Nothing} -> makePrim1 (Register initVal w) [last loopback] : (init' (n-1) loopback) where loopback = imap IntMap.! bvInstId regIn
            BV{bvPrim=prim, bvInputs=ins1, bvOutput=Nothing} -> map (makePrim1 prim) . transpose' n $ map ((imap IntMap.!) . bvInstId) ins1
            otherwise -> undefined
        ) : map (\x -> aux x nextSet imap) ins2
    where
      id = bvInstId bv
      ins2 = bvInputs bv
      nextSet = IntSet.insert id iset
      not_transpose x = transpose x

      -- Smart trick: length of result is known
      init' :: Int -> [a] -> [a]
      init' 0 _       = []
      init' n ~(x:xs) = x : init' (n-1) xs

      transpose' :: Int -> [[a]] -> [[a]]
      transpose' n [] = replicate n []
      transpose' n as = Data.List.transpose as

unroll' :: forall a b n. (Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (a -> b) -> (V.Vac n a -> V.Vac n b)
unroll' circ inps =
    ifZero @n V.newVac
    (
    V.map (unpack . FromBV)
  . (IntMap.! rootID)
  . fix
  $ aux rootBV IntSet.empty)
 where
  symb = "#retime#"
  rootBV = toBV . pack . circ . unpack $ inputPin symb
  rootID = bvInstId rootBV

  aux :: (1 <= n) => BV -> IntSet -> IntMap (V.Vac n BV) -> IntMap (V.Vac n BV)
  aux bv iset imap =
    if id `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton id (
          case bv of
            BV{bvPrim=(Input w s)} | s == symb -> V.map (toBV . pack) inps
            BV{bvPrim=(Register initVal w), bvInputs=[regIn], bvOutput=Nothing} -> updateHead (makePrim1 (Register initVal w) . Data.List.singleton) . V.rotateR $ imap IntMap.! bvInstId regIn
            BV{bvPrim=prim, bvInputs=ins1, bvOutput=Nothing} -> V.map (makePrim1 prim) . V.transposeLV $ map ((imap IntMap.!) . bvInstId) ins1
            otherwise -> undefined
        ) : map (\x -> aux x nextSet imap) ins2
    where
      id = bvInstId bv
      ins2 = bvInputs bv
      nextSet = IntSet.insert id iset

      updateHead :: forall a n. (KnownNat n, 1 <= n) => (a -> a) -> V.Vac n a -> V.Vac n a
      updateHead f = V.castShift $ \x -> V.cons (f $ V.head x) (V.tail x)

ifZero :: forall n a. KnownNat n => (n ~ 0 => a) -> (1 <= n => a) -> a
ifZero a b = case (cmpNat @0 @n Proxy Proxy, cmpNat @1 @n Proxy Proxy) of
    (EQI, GTI) -> a
    (LTI, EQI) -> b
    (LTI, LTI) -> b
    _ -> undefined
