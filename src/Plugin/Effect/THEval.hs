{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}
{-|
Module      : Plugin.Effect.THEval
Description : TemplateHaskell functions to generate wrappers.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains functions to automatically generate the correct wrapper
for functions with an arbitrary arity.
-}
module Plugin.Effect.THEval (evalGeneric, evalN) where

import Control.Monad

import Language.Haskell.TH

import Plugin.Effect.Monad

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
evalGeneric :: SearchMode -> Name -> Q Exp
evalGeneric sma fname = do
  VarI _ ty _ <- reify fname
  argsT <- collectArgs ty
  smv <- newName "sm"
  sm <- [| sma |]
  vs <- replicateM (length argsT) (newName "x")
  ev <- genEval smv fname (zip vs argsT)
  let le = LetE [ValD (VarP smv) (NormalB sm) []] ev
  if null vs
    then return le
    else return (LamE (map VarP (reverse vs)) le)

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
evalN n = do
  fname <- newName "f"
  smv <- newName "sm"
  vs <- replicateM n (newName "x")
  -- type does not matter, as long as it is not a nondeterministic function
  ev <- genEval smv fname (map (,WildCardT) vs)
  return (LamE (map VarP (smv : fname : reverse vs)) ev)

-- | Deconstruct a lifted type to collect its arguments.
collectArgs :: Type -> Q [Type]
collectArgs (AppT (AppT ArrowT ty1) ty2) = (ty1 :) <$> collectArgs ty2
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
genEval :: Name -> Name -> [(Name, Type)] -> Q Exp
genEval smv fname []               = do
  e <- [| \sm nd -> modeOp sm (allValuesNF nd) |]
  return (AppE (AppE e (VarE smv)) (VarE fname))
genEval smv fname ((v, ty) : args) = do
  lam <- [| \sm a f -> concatMap (modeOp sm . allValues . ($ a)) f |]
  wrap <- genLifting v [] ty
  inner <- genEval smv fname args
  return (AppE (AppE (AppE lam (VarE smv)) wrap) inner)

-- | Generate the lifting for the unlifted argument of a wrapper,
-- so that it matches the lifted type of the wrapped function.
genLifting :: Name -> [Name] -> Type -> Q Exp
genLifting v vs (AppT (ConT nm) (AppT (AppT ArrowT _) ty2))
 | ndName == nm = do
  -- the arg is a nondet function type, so we create the term
  -- return (\a -> rest)
  v' <- newName "a"
  rest <- genLifting v (v':vs) ty2
  ret <- [| return |]
  return (AppE ret (ParensE (LamE [VarP v'] rest)))
genLifting v vs _ = do
  -- the arg is not a nondet function type, so we apply all variables [v1..vn]
  -- we have collected to "v". If vs is empty, this is just return v, otherwise
  -- return v <*> v1 <*> ... <*> vn
  ret <- [| return |]
  app <- [| (<*>)  |]
  return (foldl (\b -> UInfixE b app . VarE) (AppE ret (VarE v)) (reverse vs))

-- | Name of the monad 'Nondet' used in the lifting.
ndName :: Name
ndName = ''Nondet
