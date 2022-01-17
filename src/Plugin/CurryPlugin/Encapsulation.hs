{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE FlexibleContexts #-}
{-|
Module      : Plugin.CurryPlugin.Encapsulation
Description : Encapsulation of Nondeterminism
Copyright   : (c) Kai-Oliver Prott (2020)
License     : BSD-3 Clause
Maintainer  : kai.prott@hotmail.de

This module contains functions to encapsulate the nondeterminism of
plugin-compiled functions.
-}
module Plugin.CurryPlugin.Encapsulation
  ( Nondet, SearchMode(..)
  , evalGeneric, evalN, eval, eval1, eval2
  ) where

import Plugin.CurryPlugin.THEval
import Plugin.CurryPlugin.Monad

-- | Evaluate a nullary nondeterministic function
-- with the given search strategy.
eval :: Normalform Nondet b
     => SearchMode -> Nondet (Lifted Nondet b) -> [b]
eval = $(evalN 0)

-- | Evaluate a unary nondeterministic function
-- with the given search strategy and arguments
eval1 :: (Normalform Nondet a, Normalform Nondet b)
      => SearchMode -> Nondet (Lifted Nondet (a -> b)) -> a -> [b]
eval1 = $(evalN 1)

-- | Evaluate a 2-ary nondeterministic function
-- with the given search strategy and arguments
eval2 :: ( Normalform Nondet a, Normalform Nondet b, Normalform Nondet c)
      => SearchMode -> Nondet (Lifted Nondet (a -> b -> c)) -> a -> b -> [c]
eval2 = $(evalN 2)
