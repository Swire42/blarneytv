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

Lists with type-checked lengths
-}

module Blarney.SList (
  Blarney.SList.SList (..)

, Blarney.SList.fromList
, Blarney.SList.toList

, Blarney.SList.lazyShape
, Blarney.SList.forceCast
, Blarney.SList.replicate
, Blarney.SList.singleton
, Blarney.SList.append
, Blarney.SList.select
, Blarney.SList.split
, Blarney.SList.update
, Blarney.SList.head
, Blarney.SList.last
, Blarney.SList.tail
, Blarney.SList.init
, Blarney.SList.uncons
, Blarney.SList.take
, Blarney.SList.drop
, Blarney.SList.rotateL
, Blarney.SList.rotateR
, Blarney.SList.reverse
, Blarney.SList.zip
, Blarney.SList.unzip
, Blarney.SList.map
, Blarney.SList.foldr
, Blarney.SList.transpose
, Blarney.SList.transposeLS
, Blarney.SList.transposeSL
) where

import qualified Prelude
import Prelude (undefined, error, Maybe(..), ($), (.), (<*>))
import GHC.TypeLits
import Data.Proxy
import qualified Data.List as L

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
fromList (x:xs) = ifZero @n (error "list too large") (Cons x (fromList @(n-1) xs))

toList :: forall n a. KnownNat n => SList n a -> [a]
toList xs = ifZero @n [] (let Cons y ys = xs in y : toList @(n-1) ys)

instance (Prelude.Show [a], KnownNat n) => Prelude.Show (SList n a) where
  show = Prelude.show . toList

instance KnownNat n => Prelude.Functor (SList n) where
  fmap = map

instance KnownNat n => Prelude.Foldable (SList n) where
  foldr = foldr

instance KnownNat n => Prelude.Traversable (SList n) where
  traverse f xss = ifZero @n (Prelude.pure Nil) (let (Cons x xs) = xss in Prelude.pure Cons <*> f x <*> Prelude.traverse f xs)

lazyShape :: forall n a. KnownNat n => SList n a -> SList n a
lazyShape xss = ifZero @n Nil (let Cons x xs = xss in Cons x xs)

forceCast :: forall n m a. (KnownNat n, KnownNat m) => SList m a -> SList n a
forceCast xs = ifEq @n @m xs (error "sizes don't match")

replicate :: forall n a. KnownNat n => a -> SList n a
replicate x = ifZero @n Nil (Cons x (replicate @(n-1) x))

singleton :: a -> SList 1 a
singleton x = Cons x Nil

append :: forall n m a. KnownNat n => SList n a -> SList m a -> SList (n+m) a
append xss ys = ifZero @n ys (let (Cons x xs) = xss in Cons x (append xs ys))

select :: forall i n a. (KnownNat i, KnownNat n, (i+1) <= n) => SList n a -> a
select xs = ifZero @n undefined (let (Cons y ys) = xs in ifZero @i y (select @(i-1) ys))

split :: forall n n0 n1 a. (KnownNat n, KnownNat n0, KnownNat n1, n1 ~ (n-n0), n0 <= n) => SList n a -> (SList n0 a, SList n1 a)
split xs = ifZero @n0 (Nil, xs) ((let (Cons h t) = xs in let (as, bs) = split @(n-1) @(n0-1) @n1 t in (Cons h as, bs)) :: (1 <= n) => (SList n0 a, SList n1 a))

update :: forall i n a. (KnownNat i, (i+1) <= n, 1 <= n) => (a -> a) -> SList n a -> SList n a
update f (Cons x xs) = ifZero @i (Cons (f x) xs) (Cons x (update @(i-1) f xs))

head :: (1 <= n) => SList n a -> a
head (Cons x _) = x

last :: forall n a. (KnownNat n, 1 <= n) => SList n a -> a
last (Cons x xs) = ifZero @(n-1) x (last xs)

tail :: (1 <= n) => SList n a -> SList (n-1) a
tail (Cons _ xs) = xs

init :: forall n a. (KnownNat n, 1 <= n) => SList n a -> SList (n-1) a
init xs = ifZero @(n-1) Nil (let Cons y ys = xs in Cons y (init ys))

uncons :: (1 <= n) => SList n a -> (a, SList (n-1) a)
uncons xs = (head xs, tail xs)

take :: forall i n a. (KnownNat i, i <= n) => SList n a -> SList i a
take xs = ifZero @i Nil ((let (Cons h t) = xs in Cons h (take @(i-1) t)) :: (1 <= n) => SList i a)

drop :: forall n i a. (KnownNat n, KnownNat i, i <= n) => SList n a -> SList (n-i) a
drop xs = ifZero @(i) xs ((let (Cons _ t) = xs in (drop @(n-1) @(i-1) t :: (i-1 <= n-1) => SList (n-i) a)) :: (1 <= n) => SList (n-i) a)

rotateL :: forall n a. (KnownNat n, 1 <= n) => SList n a -> SList n a
rotateL xs = (tail xs) `append` singleton (head xs)

rotateR :: forall n a. (KnownNat n, 1 <= n) => SList n a -> SList n a
rotateR xs = last xs `Cons` init xs

reverse :: KnownNat n => SList n a -> SList n a
reverse = aux Nil
  where
    aux :: forall n0 n1 n a. (KnownNat n0, KnownNat n1, n0+n1 ~ n) => SList n0 a -> SList n1 a -> SList n a
    aux acc xss = ifZero @n1 acc (let (Cons x xs) = xss in aux xs (Cons @(n0+1) x acc))

zip :: forall n a b. KnownNat n => SList n a -> SList n b -> SList n (a, b)
zip xss yss = ifZero @n Nil (let (Cons x xs, Cons y ys) = (xss, yss) in Cons (x, y) (zip xs ys))

unzip :: forall n a b. KnownNat n => SList n (a, b) -> (SList n a, SList n b)
unzip xyss = ifZero @n (Nil, Nil) (let (Cons (x, y) xys) = xyss in let (xs, ys) = unzip xys in (Cons x xs, Cons y ys))

map :: forall n a b. KnownNat n => (a -> b) -> SList n a -> SList n b
map f xss = ifZero @n Nil (let (Cons x xs) = xss in Cons (f x) (map f xs))

foldr :: forall n a b. KnownNat n => (a -> b -> b) -> b -> SList n a -> b
foldr f e xss = ifZero @n e (let (Cons x xs) = xss in x `f` foldr f e xs)

transpose :: forall m n a. (KnownNat n, KnownNat m) => SList m (SList n a) -> SList n (SList m a)
transpose x = ifZero @n Nil (let (y, ys) = unzip . map (uncons) $ x in Cons y (transpose ys))

transposeLS :: forall n a. KnownNat n => [SList n a] -> SList n [a]
transposeLS x = ifZero @n Nil (let (y, ys) = L.unzip . L.map (uncons) $ x in Cons y (transposeLS ys))

transposeSL :: forall n a. KnownNat n => SList n [a] -> [SList n a]
transposeSL x = case Prelude.fmap unzip . Prelude.mapM (L.uncons) $ x of
  Just (y, ys) -> y : transposeSL ys
  Nothing -> []
