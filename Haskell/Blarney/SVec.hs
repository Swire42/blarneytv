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
Module      : Blarney.SVec
Description : Spatial vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Spatial vectors
-}

module Blarney.SVec (
  Blarney.SVec.SVec,

  Blarney.SVec.toSList,
  Blarney.SVec.fromSList,
  Blarney.SVec.toList,
  Blarney.SVec.fromList,

  Blarney.SVec.lazyShape,
  Blarney.SVec.forceCast,

  Blarney.SVec.replicate,
  Blarney.SVec.iterate,
  Blarney.SVec.empty,
  Blarney.SVec.singleton,
  Blarney.SVec.append,
  Blarney.SVec.concat,
  Blarney.SVec.unconcat,
  Blarney.SVec.select,
  Blarney.SVec.split,
  Blarney.SVec.update,
  Blarney.SVec.head,
  Blarney.SVec.last,
  Blarney.SVec.tail,
  Blarney.SVec.init,
  Blarney.SVec.cons,
  Blarney.SVec.uncons,
  Blarney.SVec.take,
  Blarney.SVec.drop,
  Blarney.SVec.rotateL,
  Blarney.SVec.rotateR,
  Blarney.SVec.reverse,
  Blarney.SVec.zip,
  Blarney.SVec.unzip,
  Blarney.SVec.map,
  Blarney.SVec.zipWith,
  Blarney.SVec.foldr,
  Blarney.SVec.foldl,
  Blarney.SVec.foldr1,
  Blarney.SVec.foldl1,

  Blarney.SVec.unroll,
) where

import Prelude
import qualified Data.List as L
import Control.Arrow ((***), (&&&), first, second)

import GHC.TypeLits

import qualified Blarney.SList as SList
import Blarney.Core.BV
import Blarney.Core.Bit
import Blarney.Core.Bits
import Blarney.Core.Interface
import Blarney.ITranspose
import qualified Blarney.Retime as Retime

data SVec (n :: Nat) a = SVec { toSList :: SList.SList n a }

fromSList :: SList.SList n a -> SVec n a
fromSList = SVec

toList :: KnownNat n => SVec n a -> [a]
toList = SList.toList . toSList

fromList :: KnownNat n => [a] -> SVec n a
fromList = fromSList . SList.fromList

instance (KnownNat n, Bits a) => Bits (SVec n a) where
  type SizeOf (SVec n a) = n * SizeOf a

  sizeOf :: SVec n a -> Int
  sizeOf xs = valueOf @n * sizeOf (error "sizeOf: _|_ " :: a)

  pack :: SVec n a -> Bit (SizeOf (SVec n a))
  pack x
    | null xs = FromBV $ constBV 0 0
    | otherwise = FromBV $ L.foldr1 concatBV $
                    fmap toBV $ fmap pack $ L.reverse xs
    where xs = toList x

  unpack :: Bit (SizeOf (SVec n a)) -> SVec n a
  unpack x = fromList xs
    where
      len = valueOf @n
      xs  = [ let bits = unsafeSlice ((w*i)-1, w*(i-1)) x
                  elem = unpack bits
                  w    = sizeOf elem
              in elem
            | i <- [1..len] ]

  nameBits :: String -> SVec n a -> SVec n a
  nameBits nm = fromSList . SList.map (\(i, b) -> nameBits (nm ++ "_vec_" ++ show i) b) . SList.zip (SList.iterate (+1) 0) . toSList

instance (KnownNat n, Interface a) => Interface (SVec n a) where
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

lazyShape :: forall n a. KnownNat n => SVec n a -> SVec n a
lazyShape = fromSList . SList.lazyShape . toSList

forceCast :: forall n m a. (KnownNat n, KnownNat m) => SVec m a -> SVec n a
forceCast = fromSList . SList.forceCast . toSList

replicate :: forall n a. KnownNat n => a -> SVec n a
replicate = fromSList . SList.replicate

iterate :: forall n a. KnownNat n => (a -> a) -> a -> SVec n a
iterate f = fromSList . SList.iterate f

empty :: SVec 0 a
empty = fromSList SList.Nil

singleton :: a -> SVec 1 a
singleton = fromSList . SList.singleton

append :: forall n m a. KnownNat n => SVec n a -> SVec m a -> SVec (n+m) a
append xs ys = fromSList $ SList.append (toSList xs) (toSList ys)

concat :: forall n m a. (KnownNat n, KnownNat m) => SVec n (SVec m a) -> SVec (n*m) a
concat = fromSList . SList.concat . SList.map toSList . toSList

unconcat :: forall n m a. (KnownNat n, KnownNat m) => SVec (n*m) a -> SVec n (SVec m a)
unconcat = fromSList . SList.map fromSList . SList.unconcat . toSList

select :: forall i n a. (KnownNat i, KnownNat n, (i+1) <= n) => SVec n a -> a
select = SList.select @i @n . toSList

split :: forall n n0 n1 a. (KnownNat n, KnownNat n0, KnownNat n1, n1 ~ (n-n0), n0 <= n) => SVec n a -> (SVec n0 a, SVec n1 a)
split = (fromSList *** fromSList) . SList.split . toSList

update :: forall i n a. (KnownNat i, (i+1) <= n, 1 <= n) => (a -> a) -> SVec n a -> SVec n a
update f = fromSList . SList.update @i @n f . toSList

head :: (1 <= n) => SVec n a -> a
head = SList.head . toSList

last :: forall n a. (KnownNat n, 1 <= n) => SVec n a -> a
last = SList.last . toSList

tail :: (1 <= n) => SVec n a -> SVec (n-1) a
tail = fromSList . SList.tail . toSList

init :: forall n a. (KnownNat n, 1 <= n) => SVec n a -> SVec (n-1) a
init = fromSList . SList.init . toSList

cons :: a -> SVec n a -> SVec (n+1) a
cons h t = fromSList $ SList.Cons h (toSList t)

uncons :: (1 <= n) => SVec n a -> (a, SVec (n-1) a)
uncons = second fromSList . SList.uncons . toSList

take :: forall i n a. (KnownNat i, i <= n) => SVec n a -> SVec i a
take = fromSList . SList.take . toSList

drop :: forall n i a. (KnownNat n, KnownNat i, i <= n) => SVec n a -> SVec (n-i) a
drop = fromSList . SList.drop . toSList

rotateL :: forall n a. (KnownNat n, 1 <= n) => SVec n a -> SVec n a
rotateL = fromSList . SList.rotateL . toSList

rotateR :: forall n a. (KnownNat n, 1 <= n) => SVec n a -> SVec n a
rotateR = fromSList . SList.rotateR . toSList

reverse :: KnownNat n => SVec n a -> SVec n a
reverse = fromSList . SList.reverse . toSList

zip :: forall n a b. KnownNat n => SVec n a -> SVec n b -> SVec n (a, b)
zip xs ys = fromSList $ SList.zip (toSList xs) (toSList ys)

unzip :: forall n a b. KnownNat n => SVec n (a, b) -> (SVec n a, SVec n b)
unzip = (fromSList *** fromSList) . SList.unzip . toSList

map :: forall n a b. KnownNat n => (a -> b) -> SVec n a -> SVec n b
map f = fromSList . SList.map f . toSList

zipWith :: KnownNat n => (a -> b -> c) -> SVec n a -> SVec n b -> SVec n c
zipWith f xs ys = fromSList $ SList.zipWith f (toSList xs) (toSList ys)

foldr :: forall n a b. KnownNat n => (a -> b -> b) -> b -> SVec n a -> b
foldr f e = SList.foldr f e . toSList

foldl :: forall n a b. KnownNat n => (b -> a -> b) -> b -> SVec n a -> b
foldl f e = SList.foldl f e . toSList

foldr1 :: forall n a b. (KnownNat n, 1 <= n) => (a -> a -> a) -> SVec n a -> a
foldr1 f = SList.foldr1 f . toSList

foldl1 :: forall n a b. (KnownNat n, 1 <= n) => (a -> a -> a) -> SVec n a -> a
foldl1 f = SList.foldl1 f . toSList

instance (KnownNat n, KnownNat m) => ITranspose (SVec m (SVec n a)) (SVec n (SVec m a)) where
  itranspose = fromSList . SList.map fromSList . itranspose . SList.map toSList . toSList

instance KnownNat n => ITranspose [SVec n a] (SVec n [a]) where
  itranspose = fromSList . itranspose . L.map toSList

instance KnownNat n => ITranspose (SVec n [a]) [SVec n a] where
  itranspose = L.map fromSList . itranspose . toSList

instance KnownNat n => ITranspose (Bit n) (SVec n (Bit 1)) where
  itranspose = fromList . toBitList

instance KnownNat n => ITranspose (SVec n (Bit 1)) (Bit n) where
  itranspose = fromBitList . toList

-- cf Retime
unroll :: forall n a b. (Bits a, Bits b, KnownNat (SizeOf a), KnownNat n) => (a -> b) -> (SVec n a -> SVec n b)
unroll f = fromSList . Retime.unroll f . toSList
