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
Module      : Blarney.TVec
Description : Temporal vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Temporal vectors.
Note: For now the implementation is a restricted API of spatial vectors

Base delays and base ticks refer to the world outside of a TVec.
Short delays and fast ticks refer to the world inside a TVec.
-}

module Blarney.TVec (
  Blarney.TVec.TVec,

  Blarney.TVec.lazyShape,
  Blarney.TVec.forceCast,

  Blarney.TVec.sweep,
  Blarney.TVec.collect,
  Blarney.TVec.flatten,
  Blarney.TVec.unflatten,
  Blarney.TVec.timeStretch,
  Blarney.TVec.replicate,
  Blarney.TVec.puls,
  Blarney.TVec.countingMux,
  Blarney.TVec.update,
  Blarney.TVec.zip,
  Blarney.TVec.unzip,
  Blarney.TVec.map,
  Blarney.TVec.zipWith,
  Blarney.TVec.shift,
  Blarney.TVec.shiftReset,
  Blarney.TVec.fullDelay,
  Blarney.TVec.scan,
  Blarney.TVec.scanReset,
) where

import Prelude hiding (replicate, map, zip, zipWith)
import qualified Data.List as L
import Control.Arrow ((***), (&&&), first, second)

import GHC.TypeLits

import qualified Blarney.SList as SList
import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import Blarney.Core.Interface
import Blarney.ITranspose
import qualified Blarney.SVec as SVec
import Blarney.Core.Prelude

data TVec (n :: Nat) a = TVec { toSList :: SList.SList n a }

fromSList :: SList.SList n a -> TVec n a
fromSList = TVec

toList :: KnownNat n => TVec n a -> [a]
toList = SList.toList . toSList

fromList :: KnownNat n => [a] -> TVec n a
fromList = fromSList . SList.fromList

-- Probably useless: Make underlying container lazy in shape
lazyShape :: forall n a. KnownNat n => TVec n a -> TVec n a
lazyShape = fromSList . SList.lazyShape . toSList

-- Probably useless: Assert two sizes are equal
forceCast :: forall n m a. (KnownNat n, KnownNat m) => TVec m a -> TVec n a
forceCast = fromSList . SList.forceCast . toSList

-- Create a temporal vector by sweeping through the values of a spatial vector
sweep :: KnownNat n => SVec.SVec n a -> TVec n a
sweep = fromSList . SVec.toSList

-- Create a spatial vector by collecting values from a temporal vector
-- Note: collect . sweep === delay
collect :: (KnownNat n, Bits a) => SVec.SVec n a -> TVec n a -> SVec.SVec n a
collect init = delay init . SVec.fromSList . toSList

-- Identity
flatten :: forall n m a. (KnownNat n, KnownNat m) => TVec n (TVec m a) -> TVec (n*m) a
flatten = fromSList . SList.concat . SList.map toSList . toSList

-- Identity
unflatten :: forall n m a. (KnownNat n, KnownNat m) => TVec (n*m) a -> TVec n (TVec m a)
unflatten = fromSList . SList.map fromSList . SList.unconcat . toSList

-- Stretch time: replace every short delay by a base delay
timeStretch :: forall n a b. (KnownNat n, Bits a, Bits b) => (TVec n a -> TVec n b) -> (a -> b)
timeStretch = error "impossible with current implementation?"

-- Trivial clock domain crossing
replicate :: forall n a. KnownNat n => a -> TVec n a
replicate = fromSList . SList.replicate

-- Pulse (1) every n fast ticks, with an offset of i.
puls :: forall i n. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n) => TVec n (Bit 1)
puls = fromSList $ SList.update @i @n (\_ -> 1) $ SList.replicate 0

-- Use the value of rare instead of base every n fast ticks, with an offset of i
countingMux :: forall i n a. (KnownNat i, KnownNat n, Bits a, (i+1) <= n, 1 <= n) => TVec n a -> TVec n a -> TVec n a
countingMux rare base = zipWith (?) (puls @i @n) (zip rare base)

-- Apply f every n fast ticks, with an offset of i
update :: forall i n a. (KnownNat i, KnownNat n, Bits a, (i+1) <= n, 1 <= n) => (TVec n a -> TVec n a) -> TVec n a -> TVec n a
update f base = countingMux @i @n (f base) base

-- Wiring
zip :: forall n a b. KnownNat n => TVec n a -> TVec n b -> TVec n (a, b)
zip xs ys = fromSList $ SList.zip (toSList xs) (toSList ys)

-- Wiring
unzip :: forall n a b. KnownNat n => TVec n (a, b) -> (TVec n a, TVec n b)
unzip = (fromSList *** fromSList) . SList.unzip . toSList

-- Apply slowed-down circuit
map :: forall n a b. KnownNat n => (a -> b) -> TVec n a -> TVec n b
map f = fromSList . SList.map f . toSList

-- Merge using slowed-down circuit
zipWith :: KnownNat n => (a -> b -> c) -> TVec n a -> TVec n b -> TVec n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

-- Merge using potentialy stateful circuit
zipWithRaw :: KnownNat n => (a -> b -> c) -> TVec n a -> TVec n b -> TVec n c
zipWithRaw f xs ys = fromSList $ SList.map (uncurry f) $ toSList $ zip xs ys

-- Short delay, "shifting" values one fast tick toward the future,
-- with a constant value for the first ever fast tick
shift :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> TVec n a -> TVec n a
shift init = fromSList . SList.update @0 @n (delay init) . SList.rotateR . toSList

-- Short delay, "shifting" values one fast tick toward the future,
-- resetting to a dynamic value every n fast ticks.
-- init[i] is used iff i%n == 0
-- Tip: init can typically be `replicate cst`
shiftReset :: forall n a. (KnownNat n, Bits a, 1 <= n) => TVec n a -> TVec n a -> TVec n a
shiftReset init = countingMux @0 init . shift dontCare

-- Composed short delays, "shifting" values one whole base tick toward the future
fullDelay :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> TVec n a -> TVec n a
fullDelay init x = Prelude.iterate (shift @n init) x !! (valueOf @n)

-- Compute iterations of a circuit without slowing it down
-- Output: [init `f` x[0], (init `f` x[0]) `f` x[1], ...]
scan :: forall n a b. (KnownNat n, Bits b, 1 <= n) => (b -> a -> b) -> b -> TVec n a -> TVec n b
scan f init x = let ret = zipWithRaw f (shift init ret) x in ret

-- Compute iterations of a circuit without slowing it down,
-- Resetting loopback every n fast ticks
-- init[i] is used iff i%n == 0
-- Output: [init[0] `f` x[0], (init[0] `f` x[0]) `f` x[1], ..., init[n] `f` x[n], ...]
scanReset :: forall n a b. (KnownNat n, Bits b, 1 <= n) => (b -> a -> b) -> TVec n b -> TVec n a -> TVec n b
scanReset f init x = let ret = zipWithRaw f (shiftReset init ret) x in ret
