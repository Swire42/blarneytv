{-# LANGUAGE UndecidableSuperClasses #-}

{-|
Module      : Blarney.ITranspose
Description : Involutive transposition
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Involutive transposition, as opposed to Data.List.transpose which is not involutive.
itranspose . itranspose = id
-}

module Blarney.ITranspose where

class ITranspose b a => ITranspose a b where
  itranspose :: a -> b
