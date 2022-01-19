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
  ( evalGeneric, evalN, eval, eval1, eval2
  ) where

import Plugin.CurryPlugin.THEval
import Plugin.CurryPlugin.Monad

-- | Evaluate a nullary nondeterministic function
-- with the given search strategy.
eval :: a
eval = undefined

-- | Evaluate a unary nondeterministic function
-- with the given search strategy and arguments
eval1 :: a
eval1 = undefined

-- | Evaluate a 2-ary nondeterministic function
-- with the given search strategy and arguments
eval2 :: a
eval2 = undefined
