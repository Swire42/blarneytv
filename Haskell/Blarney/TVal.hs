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
Module      : Blarney.TVal
Description : Normally clocked values that behave as temporal vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Blarney.TVal (
  Blarney.TVal.TVal,

  Blarney.TVal.flatten,
  Blarney.TVal.unflatten,
  Blarney.TVal.puls,
  Blarney.TVal.countingMux,
  Blarney.TVal.update,
  Blarney.TVal.zip,
  Blarney.TVal.unzip,
  Blarney.TVal.map,
  Blarney.TVal.liftRaw,
  Blarney.TVal.zipWith,
  Blarney.TVal.shift,
  Blarney.TVal.shiftReset,
  Blarney.TVal.fullDelay,
  Blarney.TVal.scan,
  Blarney.TVal.scanReset,
) where

import Prelude hiding (replicate, map, zip, zipWith)
import qualified Data.List as L
import Control.Arrow ((***), (&&&), first, second)

import GHC.TypeLits
import Data.Proxy

import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import Blarney.Core.Interface
import Blarney.ITranspose
import Blarney.Retime
import Blarney.Core.Prelude

ifZero :: forall n a. KnownNat n => (n ~ 0 => a) -> (1 <= n => a) -> a
ifZero a b = case (cmpNat @0 @n Proxy Proxy, cmpNat @1 @n Proxy Proxy) of
  (EQI, GTI) -> a
  (LTI, EQI) -> b
  (LTI, LTI) -> b
  _ -> undefined

ifEq :: forall a b v. (KnownNat a, KnownNat b) => (a ~ b => v) -> v -> v
ifEq x y = case (cmpNat @a @b Proxy Proxy) of
  EQI -> x
  _ -> y

data TVal (n :: Nat) a = TVal { unwrap :: a }

-- Identity
flatten :: forall n m a. (KnownNat n, KnownNat m) => TVal n (TVal m a) -> TVal (n*m) a
flatten = TVal . unwrap . unwrap

-- Identity
unflatten :: forall n m a. (KnownNat n, KnownNat m) => TVal (n*m) a -> TVal n (TVal m a)
unflatten = TVal . TVal . unwrap

-- Compress time: replace every base delay by a short delay
--timeCompress :: forall n a b. (KnownNat n, Bits a, Bits b) => (TVal n a -> TVal n b) -> (TVec n a -> TVec n b)
--timeCompress = error "todo"

-- Pulse (1) every n fast ticks, with an offset of i.
puls :: forall i n. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n) => TVal n (Bit 1)
puls = let ret = (\x -> L.iterate (delay 0) x !! (valueOf @i)) . (delay 1) . (\x -> L.iterate (delay 0) x !! (valueOf @(n-(i+1)))) $ ret in TVal ret

-- Use the value of rare instead of base every n fast ticks, with an offset of i
countingMux :: forall i n a. (KnownNat i, KnownNat n, Bits a, KnownNat (SizeOf a), (i+1) <= n, 1 <= n) => TVal n a -> TVal n a -> TVal n a
countingMux rare base = zipWith (?) (puls @i @n) (zip rare base)

-- Apply f every n fast ticks, with an offset of i
update :: forall i n a. (KnownNat i, KnownNat n, Bits a, KnownNat (SizeOf a), (i+1) <= n, 1 <= n) => (TVal n a -> TVal n a) -> TVal n a -> TVal n a
update f base = countingMux @i @n (f base) base

-- Wiring
zip :: forall n a b. KnownNat n => TVal n a -> TVal n b -> TVal n (a, b)
zip x y = TVal $ (unwrap x, unwrap y)

-- Wiring
unzip :: forall n a b. KnownNat n => TVal n (a, b) -> (TVal n a, TVal n b)
unzip (TVal { unwrap=(x, y) }) = (TVal x, TVal y)

-- Apply slowed-down circuit
map :: forall n a b. (KnownNat n, Bits a, KnownNat (SizeOf a), Bits b) => (a -> b) -> TVal n a -> TVal n b
map f = TVal . slowdown (valueOf @n) f . unwrap

-- Apply circuit without slowing it down
liftRaw :: forall n a b. KnownNat n => (a -> b) -> TVal n a -> TVal n b
liftRaw f = TVal . f . unwrap

-- Merge using slowed-down circuit
zipWith :: (KnownNat n, Bits a, KnownNat (SizeOf a), Bits b, KnownNat (SizeOf b), Bits c) => (a -> b -> c) -> TVal n a -> TVal n b -> TVal n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

-- Merge using circuit without slowing it down
zipWithRaw :: KnownNat n => (a -> b -> c) -> TVal n a -> TVal n b -> TVal n c
zipWithRaw f xs ys = liftRaw (uncurry f) $ zip xs ys

-- Short delay, "shifting" values one tick toward the future,
-- with a constant value for the first ever tick
shift :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> TVal n a -> TVal n a
shift init = TVal . delay init . unwrap

-- Short delay, "shifting" values one tick toward the future,
-- resetting to a dynamic value every n ticks.
-- init[i] is used iff i%n == 0
-- Tip: init can typically be `replicate cst`
shiftReset :: forall n a. (KnownNat n, Bits a, KnownNat (SizeOf a), 1 <= n) => TVal n a -> TVal n a -> TVal n a
shiftReset init = countingMux @0 init . shift dontCare

-- Composed short delays, "shifting" values one whole base tick toward the future
fullDelay :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> TVal n a -> TVal n a
fullDelay init x = Prelude.iterate (shift @n init) x !! (valueOf @n)

-- Compute iterations of a circuit without slowing it down
-- Output: [init `f` x[0], (init `f` x[0]) `f` x[1], ...]
scan :: forall n a b. (KnownNat n, Bits b, 1 <= n) => (b -> a -> b) -> b -> TVal n a -> TVal n b
scan f init x = let ret = zipWithRaw f (shift init ret) x in ret

-- Compute iterations of a circuit without slowing it down,
-- Resetting loopback every n fast ticks
-- init[i] is used iff i%n == 0
-- Output: [init[0] `f` x[0], (init[0] `f` x[0]) `f` x[1], ..., init[n] `f` x[n], ...]
scanReset :: forall n a b. (KnownNat n, Bits b, KnownNat (SizeOf b), 1 <= n) => (b -> a -> b) -> TVal n b -> TVal n a -> TVal n b
scanReset f init x = let ret = zipWithRaw f (shiftReset init ret) x in ret
