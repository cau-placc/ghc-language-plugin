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
evalGeneric :: SearchMode -> Name -> Q Exp
evalGeneric sma fname = do
  ty <- reify fname >>= \case
    VarI     _ ty _ -> return ty
    ClassOpI _ ty _ -> return ty
    _               -> fail "Only functions can be captured"
  argsT <- collectArgs ty
  vs <- replicateM (length argsT) (newName "x")
  sme <- [| sma |]
  ev <- genEval sme fname (zip vs argsT)
  if null vs
    then return ev
    else return (LamE (map VarP vs) ev)

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
  ev <- genEval (VarE smv) fname (map (,WildCardT) vs)
  return (LamE (map VarP (smv : fname : vs)) ev)

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
genEval sma fname [] = do
  rEff  <- [| \mode m -> modeOp mode (allValuesNF m) |]
  return (AppE (AppE rEff sma) (VarE fname))
genEval sma fname args = do
  rEff  <- [| \mode inn f -> modeOp mode $
                  allValuesNF (f >>= \(Func f') -> inn f') |]
  inner <- genHelp args
  return (foldl AppE rEff [sma, inner, VarE fname])
  where
    genHelp :: [(Name, Type)] -> Q Exp
    genHelp []           = error "cannot happen"
    genHelp [(v,_)]      = do
      ex <- [| \vv vx -> vx (liftE (return vv)) |]
      return (AppE ex (VarE v))
    genHelp ((v,_):rest) = do
      ex <- [| \inn vv vx -> vx (liftE (return vv)) >>= \(Func f) -> inn f |]
      inner <- genHelp rest
      return (foldl AppE ex [inner, VarE v])

-- | Name of the monad 'Nondet' used in the lifting.
ndName :: Name
ndName = ''Nondet

-- | Name of the function type '-->' used in the lifting.
funcName :: Name
funcName = ''(-->)
