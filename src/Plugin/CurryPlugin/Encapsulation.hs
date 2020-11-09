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

import Plugin.Effect.THEval
import Plugin.Effect.Monad

-- | Evaluate a nullary nondeterministic function
-- with the given search strategy.
eval :: Normalform Nondet a b
     => SearchMode -> Nondet a -> [b]
eval = $(evalN 0)

-- | Evaluate a unary nondeterministic function
-- with the given search strategy and arguments
eval1 :: (Normalform Nondet a1 a2, Normalform Nondet b1 b2)
      => SearchMode -> Nondet (a1 --> b1) -> a2 -> [b2]
eval1 = $(evalN 1)

-- | Evaluate a 2-ary nondeterministic function
-- with the given search strategy and arguments
eval2 :: ( Normalform Nondet a1 a2
         , Normalform Nondet b1 b2
         , Normalform Nondet c1 c2)
      => SearchMode -> Nondet (a1 --> b1 --> c1) -> a2 -> b2 -> [c2]
eval2 = $(evalN 2)
