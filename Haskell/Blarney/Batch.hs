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
Module      : Blarney.Batch
Description : Values that can be manipulated as serial batches.
Copyright   : (c) Victor Miquel, 2024
License     : MIT

These values are using the base clock.
-}

module Blarney.Batch (
  Blarney.Batch.Batch(unwrap),
  Blarney.Batch.wrap,
  Blarney.Batch.lazyUnwrap,

  Blarney.Batch.flatten,
  Blarney.Batch.unflatten,
  Blarney.Batch.pulse,
  Blarney.Batch.pulseMux,
  Blarney.Batch.sweepMux,
  Blarney.Batch.update,
  Blarney.Batch.zip,
  Blarney.Batch.unzip,
  Blarney.Batch.map,
  Blarney.Batch.lift,
  Blarney.Batch.zipWith,
  Blarney.Batch.shift,
  Blarney.Batch.shiftReset,
  Blarney.Batch.fullDelay,
  Blarney.Batch.scan,
  Blarney.Batch.scanReset,

  Blarney.Batch.unroll,
  Blarney.Batch.slowdown,
) where

import Prelude hiding (replicate, map, zip, unzip, zipWith)
import qualified Data.List as L
import Control.Arrow ((***), (&&&), first, second)

import Blarney.Nat

import Blarney.Core.Prelude
import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import Blarney.Core.Interface
import Blarney.ITranspose
import qualified Blarney.Retime as Retime
import qualified Blarney.SVec as V

type Vec = V.SVec

data Batch (n :: Nat) a = (1 <= n) => Batch { unwrap :: a }

wrap :: forall n a. (1 <= n) => a -> Batch n a
wrap ~x = Batch { unwrap=x }

lazyShape ~(Batch { unwrap=x }) = Batch { unwrap=x }
lazyUnwrap ~(Batch { unwrap=x }) = x

-- Identity
flatten :: forall n m a. (KnownNat n, KnownNat m, 1 <= n, 1 <= m, 1 <= n*m) => Batch n (Batch m a) -> Batch (n*m) a
flatten = wrap @(n*m) . unwrap . unwrap

-- Identity
unflatten :: forall n m a. (KnownNat n, KnownNat m, 1 <= n, 1 <= m) => Batch (n*m) a -> Batch n (Batch m a)
unflatten = wrap . wrap . unwrap

-- Pulse (1) every n fast ticks, with an offset of i.
pulse :: forall i n. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n) => Batch n (Bit 1)
pulse = let ret = (\x -> L.iterate (delay 0) x !! (valueOf @i)) . (delay 1) . (\x -> L.iterate (delay 0) x !! (valueOf @(n-(i+1)))) $ ret in wrap ret

-- Use the value of rare instead of base every n fast ticks, with an offset of i
pulseMux :: forall i n a. (KnownNat i, KnownNat n, Bits a, KnownNat (SizeOf a), (i+1) <= n, 1 <= n) => Batch n a -> Batch n a -> Batch n a
pulseMux rare base = zipWithRaw (?) (pulse @i @n) (zip rare base)

-- Iterate through the values of a Vec
sweepMux :: forall n a. (KnownNat n, Bits a, KnownNat (SizeOf a), 1 <= n) => Vec n a -> Batch n a
sweepMux = error "todo"

-- Apply f every n fast ticks, with an offset of i
update :: forall i n a. (KnownNat i, KnownNat n, Bits a, KnownNat (SizeOf a), (i+1) <= n, 1 <= n) => (Batch n a -> Batch n a) -> Batch n a -> Batch n a
update f base = pulseMux @i @n (f base) base

-- Wiring
zip :: forall n a b. (KnownNat n, 1 <= n) => Batch n a -> Batch n b -> Batch n (a, b)
zip x y = wrap $ (unwrap x, unwrap y)

-- Wiring
unzip :: forall n a b. (KnownNat n, 1 <= n) => Batch n (a, b) -> (Batch n a, Batch n b)
unzip = (wrap *** wrap) . unwrap

-- Apply slowed-down circuit
map :: forall n a b. (KnownNat n, 1 <= n, Bits a, KnownNat (SizeOf a), Bits b) => (a -> b) -> Batch n a -> Batch n b
map = slowdown

-- Apply circuit without slowing it down
lift :: forall n a b. (KnownNat n, 1 <= n) => (a -> b) -> Batch n a -> Batch n b
lift f = wrap . f . unwrap

-- Merge using slowed-down circuit
zipWith :: (KnownNat n, 1 <= n, Bits a, KnownNat (SizeOf a), Bits b, KnownNat (SizeOf b), Bits c) => (a -> b -> c) -> Batch n a -> Batch n b -> Batch n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

-- Merge using circuit without slowing it down
zipWithRaw :: (KnownNat n, 1 <= n) => (a -> b -> c) -> Batch n a -> Batch n b -> Batch n c
zipWithRaw f xs ys = lift (uncurry f) $ zip xs ys

-- Short delay, "shifting" values one tick toward the future,
-- with a constant value for the first ever tick
shift :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> Batch n a -> Batch n a
shift init x = wrap $ delay init $ lazyUnwrap x

-- Short delay, "shifting" values one tick toward the future,
-- resetting to a dynamic value every n ticks.
-- init[i] is used iff i%n == 0
-- Tip: init can typically be `replicate cst`
shiftReset :: forall n a. (KnownNat n, Bits a, KnownNat (SizeOf a), 1 <= n) => Batch n a -> Batch n a -> Batch n a
shiftReset init x = pulseMux @0 init $ shift zero (x)

-- Composed short delays, "shifting" values one whole base tick toward the future
fullDelay :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> Batch n a -> Batch n a
fullDelay init x = Prelude.iterate (shift @n init) x !! (valueOf @n)

-- Compute iterations of a circuit without slowing it down
-- Output: [fst (init `f` x[0]), fst((snd (init `f` x[0])) `f` x[1]), ...]
scan :: forall n a b c. (KnownNat n, Bits b, 1 <= n) => (b -> a -> (b, c)) -> b -> Batch n a -> Batch n c
scan f init x = let (state, ret) = unzip $ zipWithRaw f (shift init state) x in ret

-- Compute iterations of a circuit without slowing it down,
-- Resetting loopback every n fast ticks
-- init[i] is used iff i%n == 0
-- Output: [fst (init[0] `f` x[0]), fst((snd (init `f` x[0])) `f` x[1]), ..., fst (init[n] `f` x[n]), ...]
scanReset :: forall n a b c. (KnownNat n, Bits b, KnownNat (SizeOf b), 1 <= n) => (b -> a -> (b, c)) -> Batch n b -> Batch n a -> Batch n c
scanReset f init x = let (state, ret) = unzip $ zipWithRaw f (shiftReset init state) x in ret

instance (KnownNat n, 1 <= n, Bits a) => Bits (Batch n a) where
  type SizeOf (Batch n a) = SizeOf a

  sizeOf :: Batch n a -> Int
  sizeOf = sizeOf . unwrap

  pack :: Batch n a -> Bit (SizeOf (Batch n a))
  pack = pack . unwrap

  unpack :: Bit (SizeOf (Batch n a)) -> Batch n a
  unpack = wrap . unpack

  nameBits :: String -> Batch n a -> Batch n a
  nameBits nm = wrap . nameBits nm . unwrap

-- cf Retime
unroll :: forall n a b. (KnownNat n, 1 <= n, Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (Batch n a -> Batch n b) -> (Vec n a -> Vec n b)
unroll f = V.unroll (unwrap . f . wrap)

-- cf Retime
slowdown :: forall n a b. (KnownNat n, 1 <= n, Bits a, KnownNat (SizeOf a), Bits b) => (a -> b) -> (Batch n a -> Batch n b)
slowdown f = wrap . Retime.slowdown (valueOf @n) f . unwrap
