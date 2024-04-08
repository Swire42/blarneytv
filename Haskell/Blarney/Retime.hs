{-# LANGUAGE NoRebindableSyntax  #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-|
Module      : Blarney.Retime
Description : Time Transformation from Lava

This module provides the time transformation from Lava.
This transformation allows computing several cycles of a circuit in a single
cycle.
-}
module Blarney.Retime (unrollList, unrollSList, unrollS, slowdown) where

import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import qualified Blarney.SList as Slist
import qualified Blarney.SVec as SVec

-- Utils
import Blarney.Core.Prim
import Blarney.Core.Utils
import Blarney.ITranspose

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

unrollList :: (Bits a, Bits b, KnownNat (SizeOf a)) => (a -> b) -> ([a] -> [b])
unrollList circ [] = []
unrollList circ inps@(inp:_) =
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

unrollSList :: forall a b n. (Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (a -> b) -> (Slist.SList n a -> Slist.SList n b)
unrollSList circ inps = ifZero @n Slist.Nil (Slist.map (unpack . FromBV) . (IntMap.! rootID) . fix $ aux rootBV IntSet.empty)
 where
  symb = "#retime#"
  rootBV = toBV . pack . circ . unpack $ inputPin symb
  rootID = bvInstId rootBV

  aux :: (1 <= n) => BV -> IntSet -> IntMap (Slist.SList n BV) -> IntMap (Slist.SList n BV)
  aux BV{bvPrim=prim, bvInputs=inputs, bvInstId=instId} iset imap =
    if instId `IntSet.member` iset
      then IntMap.empty
      else
        IntMap.unions $ IntMap.singleton instId (
          case prim of
            Input w s | s == symb -> Slist.map (toBV . pack) inps
            Register initVal w ->
              let [input] = inputs in
              Slist.update @0 (makePrim1 (Register initVal w) . L.singleton) . Slist.rotateR $ imap IntMap.! bvInstId input
            _ -> Slist.map (makePrim1 prim) . itranspose $ map ((imap IntMap.!) . bvInstId) inputs
        ) : map (\x -> aux x (IntSet.insert instId iset) imap) inputs

unrollS :: forall a b n. (Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (a -> b) -> (SVec.SVec n a -> SVec.SVec n b)
unrollS circ = SVec.fromSList . unrollSList circ . SVec.toSList

ifZero :: forall n a. KnownNat n => (n ~ 0 => a) -> (1 <= n => a) -> a
ifZero a b = case (cmpNat @0 @n Proxy Proxy, cmpNat @1 @n Proxy Proxy) of
    (EQI, GTI) -> a
    (LTI, EQI) -> b
    (LTI, LTI) -> b
    _ -> undefined

slowdown :: (Bits a, Bits b, KnownNat (SizeOf a)) => Int -> (a -> b) -> (a -> b)
slowdown n circ inp =
    unpack
  . FromBV
  . (IntMap.! rootID)
  . fix
  $ aux rootBV IntSet.empty
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
