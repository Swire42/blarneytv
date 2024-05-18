{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE NoRebindableSyntax  #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger      #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

{-|
Module      : Blarney.SList
Description : Sized lists
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Lists with type-checked lengths
-}

module Blarney.SList (
  Blarney.SList.SList(..),

  Blarney.SList.fromList,
  Blarney.SList.toList,

  Blarney.SList.lazyShape,
  Blarney.SList.forceCast,
  Blarney.SList.replicate,
  Blarney.SList.iterate,
  Blarney.SList.singleton,
  Blarney.SList.append,
  Blarney.SList.concat,
  Blarney.SList.unconcat,
  Blarney.SList.select,
  Blarney.SList.split,
  Blarney.SList.update,
  Blarney.SList.head,
  Blarney.SList.last,
  Blarney.SList.tail,
  Blarney.SList.init,
  Blarney.SList.uncons,
  Blarney.SList.take,
  Blarney.SList.drop,
  Blarney.SList.rotateL,
  Blarney.SList.rotateR,
  Blarney.SList.reverse,
  Blarney.SList.zip,
  Blarney.SList.unzip,
  Blarney.SList.map,
  Blarney.SList.zipWith,
  Blarney.SList.foldr,
  Blarney.SList.foldl,
  Blarney.SList.foldr1,
  Blarney.SList.foldl1,
) where

import qualified Prelude
import Prelude (undefined, error, Maybe(..), ($), (.), (<*>), curry, uncurry)
import GHC.TypeLits
import Data.Proxy
import qualified Data.List as L

import Blarney.ITranspose

data SList (n :: Nat) a where
  Nil :: (n ~ 0) => SList n a
  Cons :: forall n a. (1 <= n) => a -> SList (n-1) a -> SList n a

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

assertZero :: forall n v. KnownNat n => (n ~ 0 => v) -> v
assertZero = assertEq @n @0

assertEq :: forall a b v. (KnownNat a, KnownNat b) => (a ~ b => v) -> v
assertEq x = ifEq @a @b x (error "assert failed")

fromList :: forall n a. KnownNat n => [a] -> SList n a
fromList [] = ifZero @n Nil (error "list too small")
fromList (x:xs) = ifZero @n (error "list too large") (x `Cons` fromList @(n-1) xs)

toList :: forall n a. KnownNat n => SList n a -> [a]
toList xs = ifZero @n [] (let y `Cons` ys = xs in y : toList @(n-1) ys)

instance (Prelude.Show [a], KnownNat n) => Prelude.Show (SList n a) where
  show = Prelude.show . toList

instance KnownNat n => Prelude.Functor (SList n) where
  fmap = map

instance KnownNat n => Prelude.Foldable (SList n) where
  foldr = foldr

instance KnownNat n => Prelude.Traversable (SList n) where
  traverse f xss = ifZero @n (Prelude.pure Nil) (let x `Cons` xs = xss in Prelude.pure Cons <*> f x <*> Prelude.traverse f xs)

lazyShape :: forall n a. KnownNat n => SList n a -> SList n a
lazyShape xss = ifZero @n Nil (let x `Cons` xs = xss in x `Cons` xs)

forceCast :: forall n m a. (KnownNat n, KnownNat m) => SList m a -> SList n a
forceCast xs = ifEq @n @m xs (error "sizes don't match")

replicate :: forall n a. KnownNat n => a -> SList n a
replicate x = ifZero @n Nil (x `Cons` replicate @(n-1) x)

iterate :: forall n a. KnownNat n => (a -> a) -> a -> SList n a
iterate f x = ifZero @n Nil (x `Cons` iterate @(n-1) f (f x))

singleton :: a -> SList 1 a
singleton x = x `Cons` Nil

append :: forall n m a. KnownNat n => SList n a -> SList m a -> SList (n+m) a
append xss ys = ifZero @n ys (let x `Cons` xs = xss in x `Cons` append xs ys)

concat :: forall n m a. (KnownNat n, KnownNat m) => SList n (SList m a) -> SList (n*m) a
concat xss = ifZero @n Nil (let x `Cons` xs = xss in x `append` concat xs)

unconcat :: forall n m a. (KnownNat n, KnownNat m) => SList (n*m) a -> SList n (SList m a)
unconcat xss = ifZero @n (Nil) (let (x, xs) = split @(n*m) @m xss in x `Cons` unconcat @(n-1) @m xs) 

select :: forall i n a. (KnownNat i, KnownNat n, (i+1) <= n) => SList n a -> a
select xs = ifZero @n undefined (let y `Cons` ys = xs in ifZero @i y (select @(i-1) ys))

split :: forall n n0 n1 a. (KnownNat n, KnownNat n0, KnownNat n1, n1 ~ (n-n0), n0 <= n) => SList n a -> (SList n0 a, SList n1 a)
split xss = ifZero @n0 (Nil, xss) ((let x `Cons` xs = xss in let (as, bs) = split @(n-1) @(n0-1) @n1 xs in (x `Cons` as, bs)) :: (1 <= n) => (SList n0 a, SList n1 a))

update :: forall i n a. (KnownNat i, (i+1) <= n, 1 <= n) => (a -> a) -> SList n a -> SList n a
update f (x `Cons` xs) = ifZero @i (f x `Cons` xs) (x `Cons` update @(i-1) f xs)

head :: (1 <= n) => SList n a -> a
head (x `Cons` _) = x

last :: forall n a. (KnownNat n, 1 <= n) => SList n a -> a
last (x `Cons` xs) = ifZero @(n-1) x (last xs)

tail :: (1 <= n) => SList n a -> SList (n-1) a
tail (_ `Cons` xs) = xs

init :: forall n a. (KnownNat n, 1 <= n) => SList n a -> SList (n-1) a
init xs = ifZero @(n-1) Nil (let y `Cons` ys = xs in y `Cons` init ys)

uncons :: (1 <= n) => SList n a -> (a, SList (n-1) a)
uncons xs = (head xs, tail xs)

take :: forall i n a. (KnownNat i, i <= n) => SList n a -> SList i a
take xss = ifZero @i Nil ((let x `Cons` xs = xss in x `Cons` take @(i-1) xs) :: (1 <= n) => SList i a)

drop :: forall n i a. (KnownNat n, KnownNat i, i <= n) => SList n a -> SList (n-i) a
drop xs = ifZero @(i) xs ((let _ `Cons` t = xs in (drop @(n-1) @(i-1) t :: (i-1 <= n-1) => SList (n-i) a)) :: (1 <= n) => SList (n-i) a)

rotateL :: forall n a. (KnownNat n, 1 <= n) => SList n a -> SList n a
rotateL xs = (tail xs) `append` singleton (head xs)

rotateR :: forall n a. (KnownNat n, 1 <= n) => SList n a -> SList n a
rotateR xs = last xs `Cons` init xs

reverse :: KnownNat n => SList n a -> SList n a
reverse = aux Nil
  where
    aux :: forall n0 n1 n a. (KnownNat n0, KnownNat n1, n0+n1 ~ n) => SList n0 a -> SList n1 a -> SList n a
    aux acc xss = ifZero @n1 acc (let x `Cons` xs = xss in aux @(n0+1) (x `Cons` acc) xs)

zip :: forall n a b. KnownNat n => SList n a -> SList n b -> SList n (a, b)
zip xss yss = ifZero @n Nil (let (x `Cons` xs, y `Cons` ys) = (xss, yss) in (x, y) `Cons` zip xs ys)

unzip :: forall n a b. KnownNat n => SList n (a, b) -> (SList n a, SList n b)
unzip xyss = ifZero @n (Nil, Nil) (let (x, y) `Cons` xys = xyss in let (xs, ys) = unzip xys in (x `Cons` xs, y `Cons` ys))

map :: forall n a b. KnownNat n => (a -> b) -> SList n a -> SList n b
map f xss = ifZero @n Nil (let x `Cons` xs = xss in f x `Cons` map f xs)

zipWith :: KnownNat n => (a -> b -> c) -> SList n a -> SList n b -> SList n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

foldr :: forall n a b. KnownNat n => (a -> b -> b) -> b -> SList n a -> b
foldr f e xss = ifZero @n e (let x `Cons` xs = xss in x `f` foldr f e xs)

foldl :: forall n a b. KnownNat n => (b -> a -> b) -> b -> SList n a -> b
foldl f e xss = ifZero @n e (let x `Cons` xs = xss in foldl f (e `f` x) xs)

foldr1 :: forall n a b. (KnownNat n, 1 <= n) => (a -> a -> a) -> SList n a -> a
foldr1 f xss = let x `Cons` xs = xss in ifZero @(n-1) x (x `f` foldr1 f xs)

foldl1 :: forall n a b. (KnownNat n, 1 <= n) => (a -> a -> a) -> SList n a -> a
foldl1 f xss = let x `Cons` xs = xss in foldl f x xs

instance (KnownNat n, KnownNat m) => ITranspose (SList m (SList n a)) (SList n (SList m a)) where
  itranspose :: forall m n a. (KnownNat n, KnownNat m) => SList m (SList n a) -> SList n (SList m a)
  itranspose x = ifZero @n Nil (let (y, ys) = unzip . map (uncons) $ x in y `Cons` itranspose ys)

instance KnownNat n => ITranspose [SList n a] (SList n [a]) where
  itranspose :: forall n a. KnownNat n => [SList n a] -> SList n [a]
  itranspose x = ifZero @n Nil (let (y, ys) = L.unzip . L.map (uncons) $ x in y `Cons` itranspose ys)

instance KnownNat n => ITranspose (SList n [a]) [SList n a] where
  itranspose :: forall n a. KnownNat n => SList n [a] -> [SList n a]
  itranspose x = case Prelude.fmap unzip . Prelude.mapM (L.uncons) $ x of
    Just (y, ys) -> y : itranspose ys
    Nothing -> []
