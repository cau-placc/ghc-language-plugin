{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE LambdaCase      #-}
{-|
Module      : Plugin.CurryPlugin.THEval
Description : TemplateHaskell functions to generate wrappers.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains functions to automatically generate the correct wrapper
for functions with an arbitrary arity.
-}
module Plugin.CurryPlugin.THEval (evalGeneric, evalN) where

import Control.Monad

import Language.Haskell.TH

import Plugin.CurryPlugin.Monad

-- | 'evalGeneric' encapsulates a nondeterministic computation and traverses its
--   results via the given search strategy. This encapsulation can handle
--   "simple" higher-order functions, but it requires the type of the
--   encapsulated function to be known at compile-time,
--   among other stage TemplateHaskell stage restrictions.
--   Use the less convenient 'evalN', if the type is unknown at compile-time.
--
--   Examples:
--   >>> $(evalGeneric DFS 'someNullaryFunction)
--   >>> $(evalGeneric BFS 'someUnaryFunction  ) arg1
evalGeneric :: a -> Name -> Q Exp
evalGeneric sma fname = undefined

-- | 'evalN' encapsulates a nondeterministic computation and traverses its
--   results via the given search strategy.
--   This encapsulation requires its user to specify the arity of the wrapped
--   function. It also cannot handle any higher-order functions.
--   Use the more convenient 'evalGeneric' for a better interface,
--   unless the type of the wrapped function is not known at compile-time.

--   Examples:
--   >>> $(evalN 0) DFS someNullaryFunction
--   >>> $(evalN 1) BFS someUnaryFunction   arg1
evalN :: Int -> Q Exp
evalN n = undefined

-- | Deconstruct a lifted type to collect its arguments.
collectArgs :: Type -> Q [Type]
collectArgs (AppT (AppT (ConT nm) ty1) ty2)
  | funcName == nm                = (ty1 :) <$> collectArgs ty2
collectArgs (ForallT      _ _ ty) = collectArgs ty
collectArgs (ForallVisT     _ ty) = collectArgs ty
collectArgs (AppT  (ConT nm) ty2)
  | ndName == nm                  = collectArgs ty2
collectArgs (AppKindT       ty _) = collectArgs ty
collectArgs (SigT           ty _) = collectArgs ty
collectArgs (ParensT          ty) = collectArgs ty
collectArgs (ImplicitParamT  _ _) = fail "Implicit params are not supported"
collectArgs _                     = return []

-- | Generate the 'allValues' part of a wrapper for a given search mode,
-- wrapped function and list of arguments.
genEval :: Exp -> Name -> [(Name, Type)] -> Q Exp
genEval sma fname [] = undefined

-- | Name of the monad 'Nondet' used in the lifting.
ndName :: Name
ndName = undefined

-- | Name of the function type '-->' used in the lifting.
funcName :: Name
funcName = undefined
