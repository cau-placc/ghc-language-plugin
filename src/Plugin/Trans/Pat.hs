{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
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
import GHC.Hs.Lit
import GHC.Hs.Expr
import GHC.Plugins hiding (substTy, extendTvSubst, getSrcSpanM)
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Types.SourceText
import GHC.Core.ConLike
import GHC.Core.TyCo.Rep
import GHC.Utils.Error
import GHC.Data.Bag
import GHC.Parser.Annotation

import Plugin.Trans.Type
import Plugin.Trans.Constr
import Plugin.Trans.Util
import Plugin.Trans.CreateSyntax

-- | Lift the types of each pattern and
-- rename variables for sharing and newtypes.
liftPattern :: TyConMap -> Type -> LPat GhcTc
            -> TcM (LPat GhcTc, [(Var, LocatedN Var)])
liftPattern = liftPat

liftPat :: TyConMap -> Type -> LPat GhcTc
        -> TcM (LPat GhcTc, [(Var, LocatedN Var)])
liftPat tcs argty (L l p) = do
  (r, vs1) <- setSrcSpanA l $ liftPat' tcs argty p
  return (L l r, vs1)

liftPat' :: TyConMap -> Type -> Pat GhcTc
         -> TcM (Pat GhcTc, [(Var, LocatedN Var)])
liftPat' tcs argty (WildPat ty) = do
  -- This can only occur as a top-level pattern.
  -- This means that we should not wrap the type in Nondet.
  (, []) . WildPat <$> liftInnerTyTcM tcs argty ty
liftPat' tcs argty (VarPat x (L l v)) = do
  u <- getUniqueM
  -- Here we use liftType and not liftInnerType, because this pattern
  -- is guaranteed to not be the top-level pattern after pattern matching.
  -- Thus, the type of this variable really is wrapped in Nondet.
  ty <- liftTypeTcM tcs argty (varType v)
  let vnew = setVarUnique (setVarType v ty) u
  let vold = setVarType v ty
  return (VarPat x (L l vnew), [(vnew, L l vold)])
liftPat' tcs argty (LazyPat x p) = do
  (p', vars1) <- liftPat tcs argty p
  return (LazyPat x p', vars1)
liftPat' _ _ p@AsPat {} =
  panicAny "As-pattern should have been desugared before lifting" p
liftPat' tcs argty (ParPat x p) = do
  (p', vars1) <- liftPat tcs argty p
  return (ParPat x p', vars1)
-- ignore any leftover bangs, their strictness is ensured during
-- the pattern match compilation
liftPat' tcs argty (BangPat _ p) = do
  (p', vars1) <- liftPat tcs argty p
  return (unLoc p', vars1)
liftPat' _ _ p@(ListPat (ListPatTc _ Nothing) _) =
  panicAny "List pattern should have been desugared before lifting" p
liftPat' _ _ p@(ListPat (ListPatTc _ (Just _)) _) = do
  l <- getSrcSpanM
  reportError (mkMsgEnvelope l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs argty (TuplePat tys args box) = do
  con <- liftIO (getLiftedCon (tupleDataCon box (length tys)) tcs)
  let lc = noLocA (RealDataCon con)
  (args', vs) <- unzip <$> mapM (liftPat tcs argty) args
  tys' <- mapM (liftInnerTyTcM tcs argty) tys
  let det = PrefixCon [] args'
  let res = ConPat (ConPatTc tys' [] [] (EvBinds emptyBag) WpHole) lc det
  return (res, concat vs)
liftPat' _ _ p@SumPat {} = do
  l <- getSrcSpanM
  reportError (mkMsgEnvelope l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs argty p@ConPat { pat_con_ext = x@ConPatTc { cpt_arg_tys = tys }
                            , pat_args = args
                            , pat_con = L l (RealDataCon con) } = do
  let recParent = RecSelData (dataConTyCon con)
  (args', varsS) <- liftConDetail tcs argty recParent args
  -- The tys are basically type applications for the tyvars of con,
  -- so we have to use liftInnerTy.
  tys' <- mapM (liftInnerTyTcM tcs argty) tys
  con' <- L l . RealDataCon <$> liftIO (getLiftedCon con tcs)
  mty <- mkTyConTy <$> getMonadTycon
  let x' = x { cpt_arg_tys = mty:tys' }
  let p' = p { pat_args = args', pat_con_ext = x', pat_con = con' }
  return (p', varsS)
liftPat' _ _ p@ConPat {} = do
  l <- getSrcSpanM
  reportError (mkMsgEnvelope l neverQualify
    "Pattern synonyms are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ _ p@(ViewPat _ _ _) = do
  l <- getSrcSpanM
  reportError (mkMsgEnvelope l neverQualify
    "View patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ _ p@(SplicePat _ _) = do
  l <- getSrcSpanM
  reportError (mkMsgEnvelope l neverQualify
    "Spliced patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _  _ (LitPat _ (HsIntPrim _ i)) = do
  neg <- liftQ [| negate :: Int -> Int |]
  negTy <- unLoc <$> mkApp (mkNewAny neg) (intTy `mkVisFunTyMany` intTy) []
  let negSyn | i < 0    = Just (SyntaxExprTc negTy [WpHole] WpHole)
             |otherwise = Nothing
  eq <- liftQ [| (==) :: Int -> Int -> Bool |]
  let eqTy = mkVisFunTys [Scaled Many intTy, Scaled Many intTy] boolTy
  eqTyped <- unLoc <$> mkApp (mkNewAny eq) eqTy []
  let eqSyn = SyntaxExprTc eqTyped [WpHole, WpHole] WpHole
  witness <- liftQ [| fromInteger i :: Int |]
  witnessTy <- unLoc <$> mkApp (mkNewAny witness) intTy []
  let integralLit = HsIntegral (IL (SourceText (show (abs i))) False (abs i))
  let overLit = OverLit (OverLitTc False intTy) integralLit witnessTy
  return (NPat intTy (noLoc overLit) negSyn eqSyn, [])
liftPat' _ _ p@(LitPat _ _)  = return (p, [])
liftPat' _ _ p@NPat {}       = return (p, [])
liftPat' _ _ p@(NPlusKPat _ _ _ _ _ _) = do
  l <- getSrcSpanM
  reportError (mkMsgEnvelope l neverQualify
    "N+k patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs argty (SigPat _ p _) = liftPat' tcs argty (unLoc p)
liftPat' tcs argty (XPat (CoPat _ p _)) = liftPat' tcs argty p

liftConDetail :: TyConMap -> Type -> RecSelParent -> HsConPatDetails GhcTc
              -> TcM (HsConPatDetails GhcTc, [(Var, LocatedN Var)])
liftConDetail tcs argty _ (PrefixCon _ args) = do
  (args', vs) <- unzip <$> mapM (liftPat tcs argty) args
  return (PrefixCon [] args', concat vs)
liftConDetail tcs argty p (RecCon (HsRecFields flds d)) = do
  (flds', vs) <- unzip <$> mapM (liftRecFld tcs argty p) flds
  return (RecCon (HsRecFields flds' d), concat vs)
liftConDetail tcs argty _ (InfixCon arg1 arg2) = do
  (arg1', vs1) <- liftPat tcs argty arg1
  (arg2', vs2) <- liftPat tcs argty arg2
  return (InfixCon arg1' arg2', vs1 ++ vs2)

liftRecFld :: TyConMap -> Type -> RecSelParent -> LHsRecField GhcTc (LPat GhcTc)
           -> TcM (LHsRecField GhcTc (LPat GhcTc), [(Var, LocatedN Var)])
liftRecFld tcs argty p (L l1 (HsRecField x (L l2 idt) pat pn)) = do
  idt' <- liftFieldOcc tcs p idt
  (p', vs) <- liftPat tcs argty pat
  return (L l1 (HsRecField x (L l2 idt') p' pn), vs)

liftFieldOcc :: TyConMap -> RecSelParent -> FieldOcc GhcTc
             -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs p (FieldOcc v _) = do
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  stc <- getShareClassTycon
  ftc <- getFunTycon
  v' <- liftIO (getLiftedRecSel stc ftc mty us tcs p v)
  return (FieldOcc v' (noLocA (nameRdrName (varName v'))))
