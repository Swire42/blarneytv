{-# LANGUAGE NoRebindableSyntax  #-}

{-|
Module      : Blarney.Core.Retime
Description : Time Transformation from Lava

This module provides the time transformation from Lava.
This transformation allows computing several cycles of a circuit in a single
cycle.
-}
module Blarney.Core.Retime (unroll) where

import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits

-- Utils
import Blarney.Core.Prim
import Blarney.Core.Utils

-- Standard imports
import Prelude
import Data.Proxy
import GHC.TypeLits
import GHC.Generics

import Data.List
  ( transpose
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
      transpose' n as = transpose as
