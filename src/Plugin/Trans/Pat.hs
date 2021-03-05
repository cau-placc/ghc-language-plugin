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
import GHC.Hs.Extension
import GHC.Hs.Type
import GHC.Plugins hiding (substTy, extendTvSubst, getSrcSpanM)
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Core.ConLike
import GHC.Utils.Error
import GHC.Data.Bag

import Plugin.Trans.Type
import Plugin.Trans.Constr
import Plugin.Trans.Util

-- | Lift the types of each pattern and
-- rename variables for sharing and newtypes.
liftPattern :: TyConMap -> LPat GhcTc
            -> TcM (LPat GhcTc, [(Var, Var)])
liftPattern = liftPat

liftPat :: TyConMap -> LPat GhcTc
        -> TcM (LPat GhcTc, [(Var, Var)])
liftPat tcs (L l p) = do
  (r, vs1) <- setSrcSpan l $ liftPat' tcs p
  return (L l r, vs1)

liftPat' :: TyConMap -> Pat GhcTc
         -> TcM (Pat GhcTc, [(Var, Var)])
liftPat' tcs (WildPat ty) =
  -- This can only occur as a top-level pattern.
  -- This means that we should not wrap the type in Nondet.
  (, []) . WildPat <$> liftInnerTyTcM tcs ty
liftPat' tcs (VarPat x (L l v)) = do
  u <- getUniqueM
  -- Here we use liftType and not liftInnerType, because this pattern
  -- is guaranteed to not be the top-level pattern after pattern matching.
  -- Thus, the type of this variable really is wrapped in Nondet.
  ty <- liftTypeTcM tcs (varType v)
  let vnew = setVarUnique (setVarType v ty) u
  let vold = setVarType v ty
  return (VarPat x (L l vnew), [(vnew, vold)])
liftPat' tcs (LazyPat x p) = do
  (p', vars1) <- liftPat tcs p
  return (LazyPat x p', vars1)
liftPat' _ p@AsPat {} =
  panicAny "As-pattern should have been desugared before lifting" p
liftPat' tcs (ParPat x p) = do
  (p', vars1) <- liftPat tcs p
  return (ParPat x p', vars1)
-- ignore any leftover bangs, their strictness is ensured during
-- the pattern match compilation
liftPat' tcs (BangPat _ p) = do
  (p', vars1) <- liftPat tcs p
  return (unLoc p', vars1)
liftPat' _ p@(ListPat (ListPatTc _ Nothing) _) =
  panicAny "List pattern should have been desugared before lifting" p
liftPat' _ p@(ListPat (ListPatTc _ (Just _)) _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs (TuplePat tys args box) = do
  con <- liftIO (getLiftedCon (tupleDataCon box (length tys)) tcs)
  let lc = noLoc (RealDataCon con)
  (args', vs) <- unzip <$> mapM (liftPat tcs) args
  let det = PrefixCon args'
  tys' <- mapM (liftInnerTyTcM tcs) tys
  let res = ConPat (ConPatTc tys' [] [] (EvBinds emptyBag) WpHole) lc det
  return (res, concat vs)
liftPat' _ p@SumPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs p@ConPat { pat_con_ext = x@ConPatTc { cpt_arg_tys = tys }
                        , pat_args = args
                        , pat_con = L l (RealDataCon con) } = do
  let recParent = RecSelData (dataConTyCon con)
  (args', varsS) <- liftConDetail tcs recParent args
  -- The tys are basically type applications for the tyvars of con,
  -- so we have to use liftInnerTy.
  tys' <- mapM (liftInnerTyTcM tcs) tys
  con' <- L l . RealDataCon <$> liftIO (getLiftedCon con tcs)
  let x' = x { cpt_arg_tys = tys' }
  let p' = p { pat_args = args', pat_con_ext = x', pat_con = con' }
  return (p', varsS)
liftPat' _ p@ConPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Pattern synonyms are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ p@(ViewPat _ _ _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "View patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ p@(SplicePat _ _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Spliced patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _   p@(LitPat _ _)  = return (p, [])
liftPat' _   p@NPat {}       = return (p, [])
liftPat' _   p@(NPlusKPat _ _ _ _ _ _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "N+k patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs (SigPat _ p _) = liftPat' tcs (unLoc p)
liftPat' tcs (XPat (CoPat _ p _)) = liftPat' tcs p

liftConDetail :: TyConMap -> RecSelParent -> HsConPatDetails GhcTc
              -> TcM (HsConPatDetails GhcTc, [(Var, Var)])
liftConDetail tcs _ (PrefixCon args) = do
  (args', vs) <- unzip <$> mapM (liftPat tcs) args
  return (PrefixCon args', concat vs)
liftConDetail tcs p (RecCon (HsRecFields flds d)) = do
  (flds', vs) <- unzip <$> mapM (liftRecFld tcs p) flds
  return (RecCon (HsRecFields flds' d), concat vs)
liftConDetail tcs _ (InfixCon arg1 arg2) = do
  (arg1', vs1) <- liftPat tcs arg1
  (arg2', vs2) <- liftPat tcs arg2
  return (InfixCon arg1' arg2', vs1 ++ vs2)

liftRecFld :: TyConMap -> RecSelParent -> LHsRecField GhcTc (LPat GhcTc)
           -> TcM (LHsRecField GhcTc (LPat GhcTc), [(Var, Var)])
liftRecFld tcs p (L l1 (HsRecField (L l2 idt) pat pn)) = do
  idt' <- liftFieldOcc tcs p idt
  (p', vs) <- liftPat tcs pat
  return (L l1 (HsRecField (L l2 idt') p' pn), vs)

liftFieldOcc :: TyConMap -> RecSelParent -> FieldOcc GhcTc
             -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs p (FieldOcc v _) = do
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  stc <- getShareClassTycon
  v' <- liftIO (getLiftedRecSel stc mty us tcs p v)
  return (FieldOcc v' (noLoc (nameRdrName (varName v'))))
