{-# LANGUAGE NoRebindableSyntax  #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-|
Module      : Blarney.Retime
Description : Time Transformations
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Core time transformations implemented using circuit transformations.
More user-friendly signatures are provided in other modules.
-}
module Blarney.Retime (unroll, slowdown) where

import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import qualified Blarney.SList as SList

-- Utils
import Blarney.Nat
import Blarney.Core.Prim
import Blarney.Core.Utils
import Blarney.ITranspose

-- Standard imports
import Prelude
import qualified Data.List as L
import Data.Function (fix)

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- Compute several n cycles in a single cycle.
unroll :: forall n a b. (Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (a -> b) -> (SList.SList n a -> SList.SList n b)
unroll circ inps = ifZero @n SList.Nil (SList.map (unpack . FromBV) . (IntMap.! rootID) . fix $ aux rootBV IntSet.empty)
 where
  symb = "#retime#"
  rootBV = toBV . pack . circ . unpack $ inputPin symb
  rootID = bvInstId rootBV

  aux :: (1 <= n) => BV -> IntSet -> IntMap (SList.SList n BV) -> IntMap (SList.SList n BV)
  aux BV{bvPrim=prim, bvInputs=inputs, bvInstId=instId} iset imap =
    if instId `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton instId (
          case prim of
            Input w s | s == symb -> SList.map (toBV . pack) inps
            Register initVal w ->
              let [input] = inputs in
              SList.update @0 (makePrim1 (Register initVal w) . L.singleton) . SList.rotateR $ imap IntMap.! bvInstId input
            _ -> SList.map (makePrim1 prim) . itranspose $ map ((imap IntMap.!) . bvInstId) inputs
        ) : map (\x -> aux x (IntSet.insert instId iset) imap) inputs

-- Functionaly equivalent to interlacing n copies of the circuit.
-- Example: slowdown 3 accumulate [0..] = [0, 1, 2, 0+3, 1+4, 2+6, 0+3+7, 1+4+8, 2+6+9, ...]
-- Implemented by subtituying each register by n registers in series.
slowdown :: (Bits a, Bits b, KnownNat (SizeOf a)) => Int -> (a -> b) -> (a -> b)
slowdown n circ inp = unpack . FromBV . (IntMap.! rootID) . fix $ aux rootBV IntSet.empty
 where
  rootBV :: BV = toBV . pack $ circ inp
  rootID = bvInstId rootBV

  aux :: BV -> IntSet -> IntMap BV -> IntMap BV
  aux BV{bvPrim=prim, bvInputs=inputs, bvInstId=instId} iset imap =
    if instId `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton instId (
          case prim of
            Register initVal w ->
              let [input] = inputs in
              let slowedInput = imap IntMap.! bvInstId input in
              iterate (\x -> makePrim1 (Register initVal w) [x]) slowedInput !! n
            _ -> makePrim1 prim $ map ((imap IntMap.!) . bvInstId) inputs
        ) : map (\x -> aux x (IntSet.insert instId iset) imap) inputs
