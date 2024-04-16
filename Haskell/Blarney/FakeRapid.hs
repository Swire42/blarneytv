{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE NoRebindableSyntax    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-|
Module      : Blarney.FakeRapid
Description : Fake Rapid (fast clock) using sized lists
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Emulates Rapid (fast clock) using sized lists.
A true serial data wrapper represents a value that changes `n` times within
each clock cycle.
Here this is done by replicating the logic `n` times instead.
-}

module Blarney.FakeRapid (
  Blarney.FakeRapid.Rapid,

  Blarney.FakeRapid.lazyShape,
  Blarney.FakeRapid.forceCast,

  Blarney.FakeRapid.sweep,
  Blarney.FakeRapid.collect,
  Blarney.FakeRapid.flatten,
  Blarney.FakeRapid.unflatten,
  Blarney.FakeRapid.wrap,
  Blarney.FakeRapid.unwrap,
  Blarney.FakeRapid.replicate,
  Blarney.FakeRapid.clkDiv,
  Blarney.FakeRapid.clkMul,
  Blarney.FakeRapid.zip,
  Blarney.FakeRapid.unzip,
) where

import Prelude hiding (replicate, map, zip, zipWith)
import qualified Data.List as L
import Control.Arrow ((***), (&&&), first, second)

import Blarney.Nat

import qualified Blarney.SList as SList
import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import Blarney.Core.Interface
import Blarney.ITranspose
import qualified Blarney.SVec as V
import Blarney.Core.Prelude
import Blarney.Retime
import qualified Blarney.Batch as B
import Blarney.Batch(Batch)

type Vec = V.SVec

data Rapid (n :: Nat) a = (1 <= n) => Rapid { toSList :: SList.SList n a } -- private items

-- private
fromSList :: forall n a. (1 <= n) => SList.SList n a -> Rapid n a
fromSList = Rapid

-- private
toVec :: forall n a. (1 <= n) => Rapid n a -> Vec n a
toVec = V.fromSList . toSList

-- private
fromVec :: forall n a. (1 <= n) => Vec n a -> Rapid n a
fromVec = fromSList . V.toSList

-- Probably useless: Make underlying container lazy in shape
lazyShape :: forall n a. (KnownNat n, 1 <= n) => Rapid n a -> Rapid n a
lazyShape = fromSList . SList.lazyShape . toSList

-- Probably useless: Assert two sizes are equal
forceCast :: forall n m a. (KnownNat n, 1 <= n, KnownNat m) => Rapid m a -> Rapid n a
forceCast = fromSList . SList.forceCast . toSList

-- Create a temporal vector by sweeping through the values of a spatial vector
sweep :: (KnownNat n, 1 <= n) => Vec n a -> Rapid n (Batch n a)
sweep = fromSList . SList.map B.wrap . V.toSList

-- Create a spatial vector by collecting values from a temporal vector
-- Note: collect . sweep === delay
collect :: (KnownNat n, Bits a) => Vec n a -> Rapid n (Batch n a) -> Vec n a
collect init = delay init . V.fromSList . SList.map B.unwrap . toSList

-- Casting
flatten :: forall n m a. (KnownNat n, KnownNat m, 1 <= n*m) => Rapid n (Rapid m a) -> Rapid (n*m) a
flatten = fromSList . SList.concat . SList.map toSList . toSList

-- Casting
unflatten :: forall n m a. (KnownNat n, 1 <= n, KnownNat m, 1 <= m) => Rapid (n*m) a -> Rapid n (Rapid m a)
unflatten = fromSList . SList.map fromSList . SList.unconcat . toSList

-- Casting
wrap :: a -> Rapid 1 a
wrap = fromSList . SList.singleton

-- Casting
unwrap :: Rapid 1 a -> a
unwrap = SList.head . toSList

-- Clock domain crossing
replicate :: forall n a. (KnownNat n, 1 <= n) => a -> Rapid n a
replicate = fromSList . SList.replicate

-- Clock division
clkDiv :: forall n m a b. (KnownNat n, 1 <= n, Bits a, Bits b, KnownNat (SizeOf a), KnownNat (SizeOf b)) => (Rapid n a -> Rapid n b) -> (a -> b)
clkDiv f = error "todo" -- needs enabled register transformation

-- Clock multiplication
clkMul :: forall n m a b. (KnownNat n, 1 <= n, KnownNat (SizeOf a), Bits a, Bits b) => (a -> b) -> (Rapid n a -> Rapid n b)
clkMul f = fromSList . unroll f . toSList

-- Casting
zip :: forall n a b. (KnownNat n, 1 <= n) => Rapid n a -> Rapid n b -> Rapid n (a, b)
zip xs ys = fromSList $ SList.zip (toSList xs) (toSList ys)

-- Casting
unzip :: forall n a b. (KnownNat n, 1 <= n) => Rapid n (a, b) -> (Rapid n a, Rapid n b)
unzip = (fromSList *** fromSList) . SList.unzip . toSList

-- private
map :: forall n a b. (KnownNat n, 1 <= n) => (a -> b) -> Rapid n a -> Rapid n b
map f = fromSList . SList.map f . toSList

-- private
zipWith :: (KnownNat n, 1 <= n) => (a -> b -> c) -> Rapid n a -> Rapid n b -> Rapid n c
zipWith f xs ys = map (uncurry f) $ zip xs ys
