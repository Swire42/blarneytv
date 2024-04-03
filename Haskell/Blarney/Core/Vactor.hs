{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE NoStarIsType          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

{-|
Module      : Blarney.Core.Vactor
Description : A module for handling vectors
Copyright   : (c) Alexandre Joannou, 2019-2021
License     : MIT
Maintainer  : alexandre.joannou@gmail.com
Stability   : experimental

A blarney module for handling vectors
-}

module Blarney.Core.Vactor (
  -- * Vac
  Blarney.Core.Vactor.Vac (..)
  -- * 'Vac' constructors
, Blarney.Core.Vactor.newVac
, Blarney.Core.Vactor.genVac
, Blarney.Core.Vactor.fromList
, Blarney.Core.Vactor.castShift
, Blarney.Core.Vactor.lazyShape
, Blarney.Core.Vactor.replicate
, Blarney.Core.Vactor.replicateM
, Blarney.Core.Vactor.genWith
, Blarney.Core.Vactor.genWithM
, Blarney.Core.Vactor.cons
, Blarney.Core.Vactor.nil
--
, Blarney.Core.Vactor.append
, Blarney.Core.Vactor.concat
, Blarney.Core.Vactor.select
, Blarney.Core.Vactor.split
, Blarney.Core.Vactor.update
--
, Blarney.Core.Vactor.head
, Blarney.Core.Vactor.last
, Blarney.Core.Vactor.tail
, Blarney.Core.Vactor.init
, Blarney.Core.Vactor.take
, Blarney.Core.Vactor.drop
, Blarney.Core.Vactor.takeTail
, Blarney.Core.Vactor.takeAt
--
, Blarney.Core.Vactor.rotateL
, Blarney.Core.Vactor.rotateR
, Blarney.Core.Vactor.rotateLBy
, Blarney.Core.Vactor.rotateRBy
, Blarney.Core.Vactor.reverse
--
, Blarney.Core.Vactor.elem
, Blarney.Core.Vactor.any
, Blarney.Core.Vactor.all
, Blarney.Core.Vactor.or
, Blarney.Core.Vactor.and
--
, Blarney.Core.Vactor.countElem
, Blarney.Core.Vactor.countIf
, Blarney.Core.Vactor.find
--
, Blarney.Core.Vactor.zip
, Blarney.Core.Vactor.zip3
, Blarney.Core.Vactor.zip4
, Blarney.Core.Vactor.unzip
--
, Blarney.Core.Vactor.mapElems
, Blarney.Core.Vactor.map
, Blarney.Core.Vactor.mapM
, Blarney.Core.Vactor.mapM_
, Blarney.Core.Vactor.zipWith
, Blarney.Core.Vactor.zipWithM
, Blarney.Core.Vactor.zipWithM_
, Blarney.Core.Vactor.zipWith3
, Blarney.Core.Vactor.zipWith3M
, Blarney.Core.Vactor.zipAny
, Blarney.Core.Vactor.zipWithAny
, Blarney.Core.Vactor.zipWithAny3
--
, Blarney.Core.Vactor.tree
, Blarney.Core.Vactor.tree1
--
, Blarney.Core.Vactor.foldr
, Blarney.Core.Vactor.foldl
, Blarney.Core.Vactor.foldr1
, Blarney.Core.Vactor.foldl1
--
, Blarney.Core.Vactor.scanr
, Blarney.Core.Vactor.sscanr
, Blarney.Core.Vactor.scanl
, Blarney.Core.Vactor.sscanl
--
, Blarney.Core.Vactor.transpose
, Blarney.Core.Vactor.transposeLV
, Blarney.Core.Vactor.transposeVL
-- TODOs
-- toChunks
-- shiftInAt0, shiftInAtN, shiftOutFrom0, shiftOutFromN
-- findElem, findIndex, rotateBitsBy, countOnesAlt
-- transpose, transposeLN
-- mapPairs, joinActions
-- mapAccumL, mapAccumR
) where

-- Blarney imports
import Blarney.Core.BV
import Blarney.Core.FShow
import Blarney.Core.Bits
import Blarney.Core.Bit
import Blarney.Core.Interface
import Blarney.Core.Aption
import Blarney.Core.TapeFamilies
import Blarney.Core.Prelude
import Blarney.Core.Lookup
import Blarney.Core.IfThenElse

import Prelude
import GHC.TypeLits
import GHC.Generics
import Control.Monad

import qualified Data.List as L
import qualified Data.Type.Bool as B
import Data.Type.Equality

-- | 'Vac' type
data Vac (n :: Nat) a = Vac { toList :: [a] } deriving (Generic, FShow)

instance (KnownNat n, Bits a) => Bits (Vac n a) where
  type SizeOf (Vac n a) = n * SizeOf a
  sizeOf xs = valueOf @n * sizeOf (error "sizeOf: _|_ " :: a)
  pack x
    | null xs = FromBV $ constBV 0 0
    | otherwise = FromBV $ L.foldr1 concatBV $
                    fmap toBV $ fmap pack $ L.reverse xs
    where xs = toList x
  unpack x = Vac xs
    where
      len = valueOf @n
      xs  = [ let bits = unsafeSlice ((w*i)-1, w*(i-1)) x
                  elem = unpack bits
                  w    = sizeOf elem
              in elem
            | i <- [1..len] ]
  nameBits nm xs = Vac [ nameBits (nm ++ "_vec_" ++ show i) b
                       | (i,b) <- L.zip [0..] (toList xs) ]

instance (KnownNat n, Interface a) => Interface (Vac n a) where
  toIfc vec = (tm, ty)
    where
      tm = encode (valueOf @n) (toList vec)
      ty = L.foldr IfcTypeProduct IfcTypeUnit (L.replicate (valueOf @n) t)
      t = IfcTypeField portEmpty (toIfcType (undefined :: a))
      encode 0 _ = IfcTermUnit
      encode i ~(x:xs) = IfcTermProduct (toIfcTerm x) (encode (i-1) xs)
  fromIfc term = Vac $ decode (valueOf @n) term
    where
      decode 0 _ = []
      decode i ~(IfcTermProduct x0 x1) = fromIfcTerm x0 : decode (i-1) x1

instance Functor (Vac n) where
  fmap = Blarney.Core.Vactor.map

-- | Generate a 'Vac' of size 'n' initialized with 'undefined' in each element
newVac :: forall n a. KnownNat n => Vac n a
newVac = Vac (L.replicate (valueOf @n) undefined)

-- | Generate a 'Vac' of size 'n' initialized with integers from '0' to 'n-1'
genVac :: forall n. KnownNat n => Vac n Integer
genVac = Vac (L.take (valueOf @n) [0..])

-- | Convert a list to a vector, after  size check
fromList :: forall n a. KnownNat n => [a] -> Vac n a
fromList xs
  | valueOf @n == length xs = Vac xs
  | otherwise = error ("Blarney.Core.Vactor.fromList: " ++
      "list size does not match vector size")

-- | Helper casting function for turning (n+1) into (1 <= m) => (m)
castShift :: forall n a. (1 <= n) => (Vac ((n-1)+1) a -> Vac ((n-1)+1) a) -> (Vac n a -> Vac n a)
castShift f = f

-- | Identity, but makes the shape lazy
lazyShape :: KnownNat n => Vac n a -> Vac n a
lazyShape = Blarney.Core.Vactor.take

-- | Generate a 'Vac' with each element initialized to the given value
replicate :: forall n a. KnownNat n => a -> Vac n a
replicate x = Vac (L.replicate (valueOf @n) x)

replicateM :: forall n a m. (Monad m, KnownNat n) => m a -> m (Vac n a)
replicateM x = do
  xs <- Control.Monad.replicateM (valueOf @n) x
  return $ Vac xs

-- | Generate a 'Vac' from the given function 'f' applied to integers from '0'
--   to 'n-1'
genWith :: forall n a. KnownNat n => (Integer -> a) -> Vac n a
genWith f = Vac (L.take (valueOf @n) $ L.map f [0..])

genWithM :: forall n a m. (Monad m, KnownNat n) =>
              (Integer -> m a) -> m (Vac n a)
genWithM f = do
  xs <- Control.Monad.mapM f [0 .. toInteger (valueOf @n - 1)]
  return $ Vac xs

-- | Construct a new 'Vac' from a new element and an exisiting 'Vac'. The new
--   element is the head of the new 'Vac'.
cons :: a -> Vac n a -> Vac (n+1) a
cons x xs = Vac (x : toList xs)

-- | The "nil" 'Vac'
nil :: Vac 0 a
nil = Vac []

-- | Append the second 'Vac' to the first 'Vac'
append :: Vac n a -> Vac m a -> Vac (n+m) a
append xs ys = Vac (toList xs ++ toList ys)

-- | Concatenate a 'Vac' of 'Vac's into one flattened 'Vac'
concat :: Vac m (Vac n a) -> Vac (m*n) a
concat xss = Vac (L.concatMap toList (toList xss))

-- | Select the element from a 'Vac' at the given type-level index
select :: forall i n a. (KnownNat i, (i+1) <= n) => Vac n a -> a
select xs = toList xs !! valueOf @i

-- | Return a pair of 'Vac', the first element being the 'Vac' of length 'n0'
--   prefix of the given 'Vac' of length 'n', and the second element being the
--   'Vac of length 'n1' suffix of the given 'Vac' of length 'n'
split :: forall n n0 n1 a. (KnownNat n0, (n0+n1) ~ n) =>
         Vac n a -> (Vac n0 a, Vac n1 a)
split xs = (Vac v0, Vac v1)
           where (v0, v1) = splitAt (valueOf @n0) (toList xs)

-- | Generate a new 'Vac' from the given 'Vac' with the element at index 'idx'
--   updated
update :: Vac n a -> Int -> a -> Vac n a
update xs idx x = Vac (start ++ (x:end))
                  where (start, (_:end)) = splitAt idx (toList xs)

-- | Return the head element of the given 'Vac' (element at index 0)
head :: (1 <= n) => Vac n a -> a
head = L.head . toList

-- | Return the last element of the given 'Vac' (element at last index)
last :: (1 <= n) => Vac n a -> a
last = L.last . toList

-- | Return the given 'Vac' with its head element removed
tail :: Vac (n+1) a -> Vac n a
tail xs = Vac (L.tail $ toList xs)

-- | Return the given 'Vac' with its last element removed (lazy in shape)
init :: forall n a. KnownNat n => Vac (n+1) a -> Vac n a
init = Blarney.Core.Vactor.take

-- | Return the 'Vac' composed of the first 'm' elements of the given 'Vac' (lazy in shape)
take :: forall n m a. (KnownNat m, m <= n) => Vac n a -> Vac m a
take xs = Vac (take' (valueOf @m) (toList xs))
  where
    -- L.take, but lazy on the shape
    take' 0 _       = []
    take' n ~(x:xs) = x : take' (n-1) xs

-- | Return the 'Vac' composed of the last 'm' elements of the given 'Vac'
drop :: forall n m a. (KnownNat n, KnownNat m, m <= n) => Vac n a -> Vac m a
drop xs = Vac (L.drop (valueOf @n - valueOf @m) (toList xs))
takeTail :: forall n m a. (KnownNat n, KnownNat m, m <= n) => Vac n a -> Vac m a
takeTail = Blarney.Core.Vactor.drop

-- | Return the 'Vac' composed of the 'm' elements of the given 'Vac' starting
--   at index 'idx'
takeAt :: forall n m a. (KnownNat n, KnownNat m, m <= n) =>
          Int -> Vac n a -> Vac m a
takeAt idx xs
  | valueOf @m > valueOf @n - idx = error "not enough elements"
  | otherwise = Vac (L.take (valueOf @m) end)
                where (_, end) = L.splitAt idx (toList xs)

-- | Return a 'Vac' image of the given 'Vac' with its elements rotated left by
--   one, with the head element becoming the last element
rotateL :: (1 <= n) => Vac n a -> Vac n a
rotateL xs = Vac (L.tail xss ++ [L.head xss])
             where xss = toList xs

-- | Return a 'Vac' image of the given 'Vac' with its elements rotated right by
--   one, with the last element becoming the head element
rotateR :: (KnownNat n, 1 <= n) => Vac n a -> Vac n a
rotateR = castShift $ \xs -> Blarney.Core.Vactor.cons (Blarney.Core.Vactor.last xs) (Blarney.Core.Vactor.init xs)

-- Internal function: rotate vector left/right
rotateBy :: Bits a => Bool -> Bit m -> Vac n a -> Vac n a
rotateBy left i =
    Vac
  . L.map unpack
  . L.map unsafeFromBitList
  . L.transpose
  . L.map unsafeToBitList
  . L.map (`rot` i)
  . L.map unsafeFromBitList
  . L.transpose
  . L.map unsafeToBitList
  . L.map pack
  . toList
  where rot = if left then rotr else rotl

-- | Return a 'Vac' image of the given 'Vac' with its elements rotated right by
--   'i', with the last 'i' elements becoming the first 'i' elements
rotateRBy :: Bits a => Bit m -> Vac n a -> Vac n a
rotateRBy = rotateBy False

-- | Return a 'Vac' image of the given 'Vac' with its elements rotated left by
--   'i', with the first 'i' elements becoming the last 'i' elements
rotateLBy :: Bits a => Bit m -> Vac n a -> Vac n a
rotateLBy = rotateBy True

-- | Reverse the given 'Vac'
reverse :: Vac n a -> Vac n a
reverse xs = Vac (L.reverse $ toList xs)

-- | Check that the given value is and element of the given 'Vac'
elem :: Cmp a => a -> Vac n a -> Bit 1
elem x = Blarney.Core.Vactor.any (.==. x)

-- | Check that the given predicate holds for any element of the given 'Vac'
any :: (a -> Bit 1) -> Vac n a -> Bit 1
any pred = Blarney.Core.Vactor.or . fmap pred

-- | Check that the given predicate holds for all element of the given 'Vac'
all :: (a -> Bit 1) -> Vac n a -> Bit 1
all pred = Blarney.Core.Vactor.and . fmap pred

-- | Reduces a 'Vac' of 'Bit 1' by "or-ing" its elements
or :: Vac n (Bit 1) -> Bit 1
or = Blarney.Core.Vactor.tree (.||.) false

-- | Reduces a 'Vac' of 'Bit 1' by "and-ing" its elements
and :: Vac n (Bit 1) -> Bit 1
and = Blarney.Core.Vactor.tree (.&&.) true

-- | Return the number of elements of 'Vac' which are equal to the given value
countElem :: (Cmp a, 1 <= n, _) => a -> Vac n a -> Bit (Log2Ceil n + 1)
countElem e = countIf (.==. e)

-- | Return the number of elements of 'Vac' for which the given predicate holds
countIf :: (1 <= n, _) => (a -> Bit 1) -> Vac n a -> Bit (Log2Ceil n + 1)
countIf p =
  Blarney.Core.Vactor.tree (+) 0 . fmap (\x -> if p x then 1 else 0)

-- | Return a 'some' 'Aption' with the first element in the given 'Vac' that
--   satisfies the given predicate, or 'none' if no such element is found
find :: Bits a => (a -> Bit 1) -> Vac n a -> Aption a
find p xs = L.foldl (\c x -> if p x then some x else c) none (toList xs)

-- | Return a 'Vac' of pairs of elements at the same index in both given 'Vac's
zip :: Vac n a -> Vac n b -> Vac n (a, b)
zip xs ys = Vac $ L.zip (toList xs) (toList ys)

-- | Return a 'Vac' of tuple-3 of elements at the same index in the given 'Vac's
zip3 :: Vac n a -> Vac n b -> Vac n c -> Vac n (a, b, c)
zip3 xs ys zs = Vac $ L.zip3 (toList xs) (toList ys) (toList zs)

-- | Return a 'Vac' of tuple-4 of elements at the same index in the given 'Vac's
zip4 :: Vac n a -> Vac n b -> Vac n c -> Vac n d -> Vac n (a, b, c, d)
zip4 ws xs ys zs = Vac $ L.zip4 (toList ws) (toList xs) (toList ys) (toList zs)

-- | Return a 'Vac' of pairs of elements at the same index in both given 'Vac's
--   with the resulting 'Vac' being as long as the smaller input 'Vac'
zipAny :: Vac n a -> Vac m b -> Vac (Min n m) (a, b)
zipAny xs ys = Vac $ L.zip (toList xs) (toList ys)

-- | Return a pair of 'Vac' from a given 'Vac' of pairs
unzip :: Vac n (a, b) -> (Vac n a, Vac n b)
unzip xys = (Vac xs, Vac ys)
            where (xs, ys) = L.unzip (toList xys)

-- | Appy list function to elements of vector
mapElems :: ([a] -> [b]) -> Vac n a -> Vac n b
mapElems f v
  | L.length inputs == L.length outputs = Vac outputs
  | otherwise =
      error "Blarney.Core.Vactor.onElems: function does not preserve length"
  where
    inputs = toList v
    outputs = f inputs

-- | Map a function over the given 'Vac'
map :: (a -> b) -> Vac n a -> Vac n b
map f xs = Vac $ L.map f (toList xs)

mapM :: Monad m => (a -> m b) -> Vac n a -> m (Vac n b)
mapM f xs = do
  xs <- Control.Monad.mapM f (toList xs)
  return $ Vac xs

mapM_ :: Monad m => (a -> m b) -> Vac n a -> m ()
mapM_ f xs = do
  _ <- Control.Monad.mapM f (toList xs)
  return ()

-- | Return a 'Vac', result of mapping a function over the two input 'Vac's
zipWith :: (a -> b -> c) -> Vac n a -> Vac n b -> Vac n c
zipWith f xs ys = Vac $ L.map (uncurry f) (L.zip (toList xs) (toList ys))

zipWithM :: Monad m => (a -> b -> m c) -> Vac n a -> Vac n b -> m (Vac n c)
zipWithM f xs ys = do
  zs <- Control.Monad.mapM (uncurry f) (L.zip (toList xs) (toList ys))
  return $ Vac zs

zipWithM_ :: Monad m => (a -> b -> m c) -> Vac n a -> Vac n b -> m ()
zipWithM_ f xs ys = do
  _ <- Control.Monad.mapM (uncurry f) (L.zip (toList xs) (toList ys))
  return ()

-- | Return a 'Vac', result of mapping a function over the two input 'Vac's,
--   truncated to the length of the shortest one
zipWithAny :: (a -> b -> c) -> Vac n a -> Vac m b -> Vac (Min n m) c
zipWithAny f xs ys = Vac $ L.map (uncurry f) (L.zip (toList xs) (toList ys))

-- | Return a 'Vac', result of mapping a function over the three input 'Vac's
zipWith3 :: (a -> b -> c -> d) -> Vac n a -> Vac n b -> Vac n c -> Vac n d
zipWith3 f xs ys zs = Vac $ L.map (\(x, y, z) -> f x y z)
                                  (L.zip3 (toList xs) (toList ys) (toList zs))

zipWith3M :: Monad m => (a -> b -> c -> m d) -> Vac n a -> Vac n b -> Vac n c
                        -> m (Vac n d)
zipWith3M f xs ys zs = do
  res <- Control.Monad.mapM (\(x, y, z) -> f x y z)
                      (L.zip3 (toList xs) (toList ys) (toList zs))
  return $ Vac res

-- | Return a 'Vac', result of mapping a function over the three input 'Vac's,
--   truncated to the length of the shortest one
zipWithAny3 :: (a -> b -> c -> d) -> Vac n0 a -> Vac n1 b -> Vac n2 c
            -> Vac (Min n0 (Min n1 n2)) d
zipWithAny3 f xs ys zs = Vac $ L.map (\(x, y, z) -> f x y z)
                               (L.zip3 (toList xs) (toList ys) (toList zs))

-- | Tree reduction for vectors
tree :: (a -> a -> a) -> a -> Vac n a -> a
tree f z = Blarney.Core.Prelude.tree f z . toList

-- | Tree reduction for nonempty vectors
tree1 :: (a -> a -> a) -> Vac n a -> a
tree1 f = Blarney.Core.Prelude.tree1 f . toList

-- | Reduce a 'Vac' using the given function, starting with a provided seed and
--   the last element of the 'Vac'
foldr :: (a -> b -> b) -> b -> Vac n a -> b
foldr f seed xs = L.foldr f seed (toList xs)

-- | Reduce a 'Vac' using the given function, starting with a provided seed and
--   the first element of the 'Vac'
foldl :: (b -> a -> b) -> b -> Vac n a -> b
foldl f seed xs = L.foldl f seed (toList xs)

-- | Reduce a 'Vac' using the given function, starting with the last element of
--   the 'Vac' as the seed
foldr1 :: 1 <= n => (a -> a -> a) -> Vac n a -> a
foldr1 f xs = L.foldr1 f (toList xs)

-- | Reduce a 'Vac' using the given function, starting with the first element of
--   the 'Vac' as the seed
foldl1 :: 1 <= n => (a -> a -> a) -> Vac n a -> a
foldl1 f xs = L.foldl1 f (toList xs)

-- | Reduce a 'Vac' using the given function in a tree structure
fold :: 1 <= n => (a -> a -> a) -> Vac n a -> a
fold f xs = Blarney.Core.Prelude.tree1 f (toList xs)

-- | Apply a function over a 'Vac' starting with the given seed and the last
--   element, yielding a 'Vac' one element bigger than the provided one
scanr :: (a -> b -> b) -> b -> Vac n a -> Vac (n+1) b
scanr f seed xs = Vac $ L.scanr f seed (toList xs)

-- | Apply a function over a 'Vac' starting with the given seed and the last
--   element, dropping the new last element (provided seed), effectively
--   yielding a 'Vac' of the same size as the provided one
sscanr :: (a -> b -> b) -> b -> Vac n a -> Vac (n+1) b
sscanr f seed xs = Vac $ L.init (L.scanr f seed (toList xs))

-- | Apply a function over a 'Vac' starting with the given seed and the first
--   element, yielding a 'Vac' one element bigger than the provided one
scanl :: (b -> a -> b) -> b -> Vac n a -> Vac (n+1) b
scanl f seed xs = Vac $ L.scanl f seed (toList xs)

-- | Apply a function over a 'Vac' starting with the given seed and the first
--   element, dropping the new first element (provided seed), effectively
--   yielding a 'Vac' of the same size as the provided one
sscanl :: (b -> a -> b) -> b -> Vac n a -> Vac (n+1) b
sscanl f seed xs = Vac $ L.tail (L.scanl f seed (toList xs))

-- |Index a vector using a bit vector
instance (Interface a, KnownNat n) => Lookup (Vac m a) (Bit n) a where
  v ! i = toList v ! i

-- |Index a vector using an 'Int'
instance Lookup (Vac m a) Int a where
  v ! i = toList v ! i

-- |Index a vector using an 'Integer'
instance Lookup (Vac m a) Integer a where
  v ! i = toList v ! fromIntegral i

transpose' :: forall a. Int -> [[a]] -> [[a]]
transpose' n [] = L.replicate n []
transpose' n as = L.transpose as

transpose :: forall m n a. (KnownNat n, KnownNat m) => Vac m (Vac n a) -> Vac n (Vac m a)
transpose = fromList . L.map fromList . transpose' (valueOf @n) . L.map toList . toList

transposeVL :: forall n a. KnownNat n => Vac n [a] -> [Vac n a]
transposeVL = L.map fromList . transpose' (valueOf @n) . toList

transposeLV :: forall n a. KnownNat n => [Vac n a] -> Vac n [a]
transposeLV = fromList . transpose' (valueOf @n) . L.map toList
