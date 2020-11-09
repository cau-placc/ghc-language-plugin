{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plugin.Trans.PatternMatching
Description : Lift pattern expressions
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module provides a function to lift a pattern and extract any potential
variables that might need to be shared.
-}
module Plugin.Trans.Pat (liftPattern) where

import GHC.Hs.Pat
import GHC.Hs.Types
import GHC.Hs.Extension
import GhcPlugins hiding (getSrcSpanM)
import TcRnTypes
import ConLike
import TcEvidence
import Bag
import TcRnMonad
import ErrUtils

import Plugin.Trans.Type
import Plugin.Trans.Constr
import Plugin.Trans.Util

-- | Lift the types of each pattern and
-- rename variables for sharing and newtypes.
-- The third return comoponent is only needed for newtypes
-- and is only manipulated for newtype constructors.
liftPattern :: TyConMap -> LPat GhcTc
            -> TcM (LPat GhcTc, [(Var, Var)], [(Var, Var)])
liftPattern = liftPat False

-- | To prevent returning the variables of top-level var patterns from
-- being returned as newtype-variables
-- (e.g. variables inside a newtype constructor pattern)
-- and to not lift the type of those variables
-- we remember if we are "under" a newtype or not.
liftPat :: Bool -> TyConMap -> LPat GhcTc
        -> TcM (LPat GhcTc, [(Var, Var)], [(Var, Var)])
liftPat new tcs (L l p) = do
  (r, vs1, vs2) <- setSrcSpan l $ liftPat' new tcs p
  return (L l r, vs1, vs2)

liftPat' :: Bool -> TyConMap -> Pat GhcTc
         -> TcM (Pat GhcTc, [(Var, Var)], [(Var, Var)])
liftPat' _      tcs (WildPat ty) =
  -- This can only occur as a top-level pattern.
  -- This means that we should not wrap the type in Nondet.
  (, [], []) . WildPat <$> liftInnerTyTcM tcs ty
liftPat' new tcs (VarPat x (L l v))
  -- Get a new variable based on the given one.
  -- We choose a new ID for the pattern variable, because the pattern variable
  -- will be shared while the "old" id is used
  -- for the binding variable after sharing.
  -- This aviods having to replace all mentions of the old variable in the body.
  | new = do
    u <- getUniqueM
    mty <- mkTyConTy <$> getMonadTycon
    -- For newtypes, the new variable is only lifted on the inner level,
    -- while the old one is lifted fully (we set "old = return new" later).
    ty <- liftInnerTyTcM tcs (varType v)
    let vnew = setVarType (setVarUnique v u) ty
    let vold = setVarType v (mkAppTy mty ty)
    -- Sharing not required, because this variable cannot contain any effect
    -- (except for deep effects, which do not need to be shared here).
    return (VarPat x (L l vnew), [], [(vnew, vold)])
  | otherwise = do
    u <- getUniqueM
    -- Here we use liftType and not liftInnerType, because this pattern
    -- is guaranteed to not be the top-level pattern after pattern matching.
    -- Thus, the type of this variable really is wrapped in Nondet.
    ty <- liftTypeTcM tcs (varType v)
    let vnew = setVarUnique (setVarType v ty) u
    let vold = setVarType v ty
    return (VarPat x (L l vnew), [(vnew, vold)], [])
liftPat' new tcs (LazyPat x p) = do
  (p', vars1, vars2) <- liftPat new tcs p
  return (LazyPat x p', vars1, vars2)
liftPat' _ _ p@AsPat {} =
  panicAny "As-pattern should have been desugared before lifting" p
liftPat' new tcs (ParPat x p) = do
  (p', vars1, vars2) <- liftPat new tcs p
  return (ParPat x p', vars1, vars2)
liftPat' _ _ p@BangPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Bang patterns are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
liftPat' _ _ p@(ListPat (ListPatTc _ Nothing) _) =
  panicAny "List pattern should have been desugared before lifting" p
liftPat' _ _ p@(ListPat (ListPatTc _ (Just _)) _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
liftPat' _ tcs (TuplePat tys args box) = do
  con <- liftIO (getLiftedCon (tupleDataCon box (length tys)) tcs)
  let lc = noLoc (RealDataCon con)
  (args', vs, _) <- unzip3 <$> mapM (liftPat False tcs) args
  let det = PrefixCon args'
  tys' <- mapM (liftInnerTyTcM tcs) tys
  return (ConPatOut lc tys' [] [] (EvBinds emptyBag) det WpHole, concat vs, [])
liftPat' _ _ p@SumPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
liftPat' _ _ p@ConPatIn {} =
  panicAny "Untyped pattern not expected after TC" p
liftPat' _ tcs p@ConPatOut{ pat_args = args
                        , pat_arg_tys = tys
                        , pat_con = L l (RealDataCon con) } = do
  let recParent = RecSelData (dataConTyCon con)
  let isNew = isNewTyCon (dataConTyCon con)
  (args', varsS, varsN) <- liftConDetail isNew tcs recParent args
  -- The tys are basically type applications for the tyvars of con,
  -- so we have to use liftInnerTy.
  tys' <- mapM (liftInnerTyTcM tcs) tys
  con' <- L l . RealDataCon <$> liftIO (getLiftedCon con tcs)
  let p' = p { pat_args = args', pat_arg_tys = tys', pat_con = con' }
  if isNew
    -- Vars under newtypes do not need to be shared,
    -- as their nondeterminism is already triggered.
    -- But they have to be wrapped in a return again.
    then return (p', [], varsN)
    else return (p', varsS, [])
liftPat' _ _ p@ConPatOut{ } = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Pattern synonyms are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
liftPat' _ _ p@ (ViewPat _ _ _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "View patterns are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
liftPat' _ _ p@(SplicePat _ _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Spliced patterns are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
liftPat' _   _   p@(LitPat _ _)  = return (p, [], [])
liftPat' _   _   p@NPat {}       = return (p, [], [])
liftPat' _   _   p@(NPlusKPat _ (L _ v) _ _ _ _) = do
  u <- getUniqueM
  -- An n+k pattern behaves essentially like a newtype constr pattern,
  -- as v is definitely unlifted.
  return (p, [], [(setVarUnique v u, v)])
liftPat' new tcs (SigPat _ p _) = liftPat' new tcs (unLoc p)
liftPat' new tcs (CoPat _ _ p _) = liftPat' new tcs p
liftPat' _   _   p@(XPat _) = return (p, [], [])

liftConDetail :: Bool -> TyConMap -> RecSelParent -> HsConPatDetails GhcTc
              -> TcM (HsConPatDetails GhcTc, [(Var, Var)], [(Var, Var)])
liftConDetail new tcs _ (PrefixCon args) = do
  (args', vs, vsn) <- unzip3 <$> mapM (liftPat new tcs) args
  return (PrefixCon args', concat vs, concat vsn)
liftConDetail new tcs p (RecCon (HsRecFields flds d)) = do
  (flds', vs, vsn) <- unzip3 <$> mapM (liftRecFld new tcs p) flds
  return (RecCon (HsRecFields flds' d), concat vs, concat vsn)
liftConDetail new tcs _ (InfixCon arg1 arg2) = do
  (arg1', vs1, vsn1) <- liftPat new tcs arg1
  (arg2', vs2, vsn2) <- liftPat new tcs arg2
  return (InfixCon arg1' arg2', vs1 ++ vs2, vsn1 ++ vsn2)

liftRecFld :: Bool -> TyConMap -> RecSelParent -> LHsRecField GhcTc (LPat GhcTc)
           -> TcM (LHsRecField GhcTc (LPat GhcTc), [(Var, Var)], [(Var, Var)])
liftRecFld new tcs p (L l1 (HsRecField (L l2 idt) pat pn)) = do
  idt' <- liftFieldOcc tcs p idt
  (p', vs, vsn) <- liftPat new tcs pat
  return (L l1 (HsRecField (L l2 idt') p' pn), vs, vsn)

liftFieldOcc :: TyConMap -> RecSelParent -> FieldOcc GhcTc
             -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs p (FieldOcc v _) = do
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  stc <- getShareClassTycon
  v' <- liftIO (getLiftedRecSel stc mty us tcs p v)
  return (FieldOcc v' (noLoc (nameRdrName (varName v'))))
liftFieldOcc _   _ x = return x
