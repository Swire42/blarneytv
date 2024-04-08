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
-}

module Blarney.TVec (
  Blarney.TVec.TVec,

  Blarney.TVec.lazyShape,
  Blarney.TVec.forceCast,

  Blarney.TVec.sweep,
  Blarney.TVec.collect,
  Blarney.TVec.replicate,
  Blarney.TVec.singleton,
  Blarney.TVec.puls,
  Blarney.TVec.update,
  Blarney.TVec.zip,
  Blarney.TVec.unzip,
  Blarney.TVec.map,
  Blarney.TVec.zipWith,
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

instance (KnownNat n, Bits a) => Bits (TVec n a) where
  type SizeOf (TVec n a) = n * SizeOf a

  sizeOf :: TVec n a -> Int
  sizeOf xs = valueOf @n * sizeOf (error "sizeOf: _|_ " :: a)

  pack :: TVec n a -> Bit (SizeOf (TVec n a))
  pack x
    | null xs = FromBV $ constBV 0 0
    | otherwise = FromBV $ L.foldr1 concatBV $
                    fmap toBV $ fmap pack $ L.reverse xs
    where xs = toList x

  unpack :: Bit (SizeOf (TVec n a)) -> TVec n a
  unpack x = fromList xs
    where
      len = valueOf @n
      xs  = [ let bits = unsafeSlice ((w*i)-1, w*(i-1)) x
                  elem = unpack bits
                  w    = sizeOf elem
              in elem
            | i <- [1..len] ]

  nameBits :: String -> TVec n a -> TVec n a
  nameBits nm = fromSList . SList.map (\(i, b) -> nameBits (nm ++ "_vec_" ++ show i) b) . SList.zip (SList.iterate (+1) 0) . toSList

instance (KnownNat n, Interface a) => Interface (TVec n a) where
  toIfc vec = (tm, ty)
    where
      tm = encode (valueOf @n) (toList vec)
      ty = L.foldr IfcTypeProduct IfcTypeUnit (L.replicate (valueOf @n) t)
      t = IfcTypeField portEmpty (toIfcType (undefined :: a))
      encode 0 _ = IfcTermUnit
      encode i ~(x:xs) = IfcTermProduct (toIfcTerm x) (encode (i-1) xs)
  fromIfc term = fromList $ decode (valueOf @n) term
    where
      decode 0 _ = []
      decode i ~(IfcTermProduct x0 x1) = fromIfcTerm x0 : decode (i-1) x1

lazyShape :: forall n a. KnownNat n => TVec n a -> TVec n a
lazyShape = fromSList . SList.lazyShape . toSList

forceCast :: forall n m a. (KnownNat n, KnownNat m) => TVec m a -> TVec n a
forceCast = fromSList . SList.forceCast . toSList

-- hardware impl: delays + mux
sweep :: KnownNat n => SVec.SVec n a -> TVec n a
sweep = fromSList . SVec.toSList

-- hardware impl: delays + demux
collect :: (KnownNat n, Bits a) => SVec.SVec n a -> TVec n a -> SVec.SVec n a
collect init = delay init . SVec.fromSList . toSList

-- hardware impl: clock domain crossing
replicate :: forall n a. KnownNat n => a -> TVec n a
replicate = fromSList . SList.replicate

-- hardware impl: wire
singleton :: a -> TVec 1 a
singleton = fromSList . SList.singleton

-- hardware impl: puls
puls :: forall i n. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n) => TVec n (Bit 1)
puls = fromSList $ SList.update @i @n (\_ -> 1) $ SList.replicate 0

-- hardware impl: as described
update :: forall i n a. (KnownNat i, KnownNat n, Bits a, (i+1) <= n, 1 <= n) => (a -> a) -> TVec n a -> TVec n a
update f = zipWith (\p x -> p ? (f x, x)) (puls @i @n)

-- hardware impl: wires
zip :: forall n a b. KnownNat n => TVec n a -> TVec n b -> TVec n (a, b)
zip xs ys = fromSList $ SList.zip (toSList xs) (toSList ys)

-- hardware impl: wires
unzip :: forall n a b. KnownNat n => TVec n (a, b) -> (TVec n a, TVec n b)
unzip = (fromSList *** fromSList) . SList.unzip . toSList

-- hardware impl: slowdown
map :: forall n a b. KnownNat n => (a -> b) -> TVec n a -> TVec n b
map f = fromSList . SList.map f . toSList

-- hardware impl: as described
zipWith :: KnownNat n => (a -> b -> c) -> TVec n a -> TVec n b -> TVec n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

-- hardware impl: delay
shift :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> TVec n a -> TVec n a
shift init = fromSList . SList.update @0 @n (delay init) . SList.rotateR . toSList

-- hardware impl: as described
shiftReset :: forall n a. (KnownNat n, Bits a, 1 <= n) => a -> TVec n a -> TVec n a
shiftReset init = update @0 @n (\_ -> init) . shift init
