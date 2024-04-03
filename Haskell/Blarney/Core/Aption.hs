{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE OverloadedRecordDot   #-}

{- |
Module      : Blarney.Core.Aption
Description : An 'Aption' type, similar to 'Maybe' in functionality
Copyright   : (c) Alexandre Joannou, 2019
License     : MIT
Maintainer  : alexandre.joannou@gmail.com
Stability   : experimental

An 'Aption' type, similar to 'Maybe' in functionality but represented as a pair
of a flag and a value.
-}
module Blarney.Core.Aption
  ( -- * Aption type
    Aption(..), some, none, isSome, isNone, fromAption
  ) where

-- Blarney imports
import Blarney.Core.Bit
import Blarney.Core.BV
import Blarney.Core.FShow
import Blarney.Core.Bits
import Blarney.Core.Interface
import Blarney.Core.Prelude

import Prelude
import GHC.Generics
import GHC.Records (HasField(..))

{- |
'Aption' type to wrap a value. An 'Aption t' is represented as a pair of a
'Bit 1' indicating whether the value held is valid, and a value of type 't'.
-}

data Aption t =
  Aption {
    valid :: Bit 1
  , val :: t
  } deriving (Generic, Bits, Interface, FShow, Cmp)

instance Functor Aption where
  fmap f (Aption valid value) = Aption valid (f value)

-- | Builds an 'Aption' with a valid value
some :: Bits t => t -> Aption t
some val = Aption true val

-- | Builds an invalid 'Aption'
none :: Bits t => Aption t
none = Aption false dontCare

-- | Tests if an 'Aption' is a 'some'
isSome :: Bits t => Aption t -> Bit 1
isSome opt = opt.valid

-- | Tests if an 'Aption' is a 'none'
isNone :: Bits t => Aption t -> Bit 1
isNone opt = inv opt.valid

-- | Gets the value from a valid 'Aption', or a given default value otherwise
fromAption :: Bits t => t -> Aption t -> t
fromAption dflt opt = opt.valid ? (opt.val, dflt)
