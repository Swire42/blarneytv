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
Module      : Blarney.Nat
Description : TypeLits and helper functions
Copyright   : (c) Victor Miquel, 2024
License     : MIT

These values are using the base clock.
-}

module Blarney.Nat (
  module GHC.TypeLits,
  Blarney.Nat.ifZero,
  Blarney.Nat.ifEq,
) where

import Prelude(undefined)
import GHC.TypeLits
import Data.Proxy

ifZero :: forall (n :: Nat) a. KnownNat n => (n ~ 0 => a) -> (1 <= n => a) -> a
ifZero a b = case (cmpNat @0 @n Proxy Proxy, cmpNat @1 @n Proxy Proxy) of
  (EQI, GTI) -> a
  (LTI, EQI) -> b
  (LTI, LTI) -> b
  _ -> undefined

ifEq :: forall n m a. (KnownNat n, KnownNat m) => (n ~ m => a) -> a -> a
ifEq x y = case (cmpNat @n @m Proxy Proxy) of
  EQI -> x
  _ -> y
