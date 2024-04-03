{-# LANGUAGE NoRebindableSyntax  #-}
{-# OPTIONS_GHC -fplugin=IfSat.Plugin #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-|
Module      : Blarney.Retime
Description : Time Transformation from Lava

This module provides the time transformation from Lava.
This transformation allows computing several cycles of a circuit in a single
cycle.
-}
module Blarney.Retime (unroll, unroll') where

import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import qualified Blarney.Vector as V

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

import qualified Data.List as L
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
  aux BV{bvPrim=prim, bvInputs=inputs, bvInstId=instId} iset imap =
    if instId `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton instId (
          case prim of
            Input w s | s == symb -> map (toBV . pack) inps
            Register initVal w ->
              let [input] = inputs in
              let feedback = imap IntMap.! bvInstId input in
              makePrim1 (Register initVal w) [last feedback] : (take' (n-1) feedback)
            _ -> map (makePrim1 prim) . transpose' n $ map ((imap IntMap.!) . bvInstId) inputs
        ) : map (\x -> aux x (IntSet.insert instId iset) imap) inputs
    where
      -- Like L.take, but lazy in shape
      take' :: Int -> [a] -> [a]
      take' 0 _       = []
      take' n ~(x:xs) = x : take' (n-1) xs

      transpose' :: Int -> [[a]] -> [[a]]
      transpose' n [] = replicate n []
      transpose' n as = L.transpose as

unroll' :: forall a b n. (Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (a -> b) -> (V.Vec n a -> V.Vec n b)
unroll' circ inps = ifZero @n V.nil (V.map (unpack . FromBV) . (IntMap.! rootID) . fix $ aux rootBV IntSet.empty)
 where
  symb = "#retime#"
  rootBV = toBV . pack . circ . unpack $ inputPin symb
  rootID = bvInstId rootBV

  aux :: (1 <= n) => BV -> IntSet -> IntMap (V.Vec n BV) -> IntMap (V.Vec n BV)
  aux BV{bvPrim=prim, bvInputs=inputs, bvInstId=instId} iset imap =
    if instId `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton instId (
          case prim of
            Input w s | s == symb -> V.map (toBV . pack) inps
            Register initVal w ->
              let [input] = inputs in
              updateHead (makePrim1 (Register initVal w) . L.singleton) . V.rotateR $ imap IntMap.! bvInstId input
            _ -> V.map (makePrim1 prim) . V.transposeLV $ map ((imap IntMap.!) . bvInstId) inputs
        ) : map (\x -> aux x (IntSet.insert instId iset) imap) inputs
    where
      updateHead :: forall a n. (KnownNat n, 1 <= n) => (a -> a) -> V.Vec n a -> V.Vec n a
      updateHead f = V.castShift $ \x -> V.cons (f $ V.head x) (V.tail x)

ifZero :: forall n a. KnownNat n => (n ~ 0 => a) -> (1 <= n => a) -> a
ifZero a b = case (cmpNat @0 @n Proxy Proxy, cmpNat @1 @n Proxy Proxy) of
    (EQI, GTI) -> a
    (LTI, EQI) -> b
    (LTI, LTI) -> b
    _ -> undefined
