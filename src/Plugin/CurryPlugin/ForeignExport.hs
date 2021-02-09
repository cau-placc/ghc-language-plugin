{-|
Module      : Plugin.CurryPlugin.ForeignExport
Description : Collection of foreign definitions for the Prelude
Copyright   : (c) Kai-Oliver Prott (2020)
License     : BSD-3 Clause
Maintainer  : kai.prott@hotmail.de

This module re-exports definitions that are required for the Prelude of
our Plugin. Note that we re-export Haskell's original defintions from the
Prelude of Base packages, while the built-In module is just added so that it
is loaded in every plugin-compiled module.
-}
module Plugin.CurryPlugin.ForeignExport
  ( (?), failed
  , Bool(..), Int, Integer, Char, String, Ordering(..)
  , Ratio, Rational, Float, Double
  , Show(..), Eq(..), Ord(..)
  , Num(..), Fractional(..), Real(..), Integral(..), Enum(..), Bounded(..)
  , Functor(..), Applicative(..), Alternative(..), Monad(..), MonadFail(..)
  , IsString(..)
  ) where

import Data.Ratio
import Data.String

import Control.Applicative

import Plugin.Effect.Monad
import Plugin.CurryPlugin.BuiltIn ()

{-# ANN module Nondeterministic #-}
