{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-|
Module      : Plugin.Trans.Expr
Description : Main lifting transformation for functions and expressions
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module provides the main transformation of our monadic lifting for
functions and expressions to integrate our effect.
-}
module Plugin.Trans.Expr (liftMonadicBinding, liftMonadicExpr) where

import Control.Monad
import Data.Syb
import Data.List
import Data.Tuple.Extra
import Data.Maybe
import Data.Either
import Data.Char
import Language.Haskell.Syntax.Extension

import GHC.Plugins
import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Lit
import GHC.Hs.Type
import GHC.Hs.Expr
import GHC.Core.TyCo.Rep
import GHC.Types.Id.Make
import GHC.Types.TypeEnv
import GHC.Types.Tickish
import GHC.Types.Unique
import GHC.Types.TyThing
import GHC.Tc.Types
import GHC.Tc.Solver
import GHC.Tc.Types.Origin
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.Zonk
import GHC.Tc.Utils.TcType
import GHC.Tc.Utils.TcMType
import GHC.Utils.Error
import GHC.Core.ConLike
import GHC.Core.InstEnv
import GHC.Core.Class
import GHC.Data.Bag
import GHC.Parser.Annotation
import GHC.Builtin.PrimOps
import GHC.Builtin.Types.Prim
import GHC.Builtin.Names
import GHC.Iface.Env
import GHC.Int

import Plugin.Trans.Constr
import Plugin.Trans.Coerce
import Plugin.Trans.Record
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Trans.Pat
import Plugin.Trans.Class
import Plugin.Trans.FunWiredIn
import Plugin.Trans.CreateSyntax
import Plugin.Trans.DictInstFun
import Plugin.Trans.ConstraintSolver
import Plugin.Effect.Classes (liftE)

-- | Transform the given binding with a monadic lifting to incorporate
-- our nondeterminism as an effect.
-- This function also transforms any nested bindings recursively and
-- thus needs to know whether it is a local binding or not.
-- First  Bool: This is a local binding, swap the Unique for sharing purposes
-- Second Bool: This is a nested AbsBinds, do not insert into type env
liftMonadicBinding :: Bool -> [Ct] -> Maybe Type -> TyConMap -> [ClsInst]
                   -> HsBindLR GhcTc GhcTc
                   -> TcM ([HsBindLR GhcTc GhcTc], [(Var, LocatedN Var)])
liftMonadicBinding lcl given argty' tcs _ (FunBind wrap (L b name) eqs ticks) =
  setSrcSpanA b $ addLandmarkErrCtxt ("In the definition of" <+> ppr name) $ do
  -- create the dictionary variables
  let (tvs, c) = collectTyDictArgs wrap
  stc <- getShareClassTycon
  mtc <- getMonadTycon
  ftc <- getFunTycon

  sigVar <- case argty' of
    Just (TyVarTy v) -> return v
    _                -> error "TODO"
  let argty = mkTyVarTy sigVar
  let mty = mkTyConApp mtc [argty]
  uss <- replicateM (length tvs) getUniqueSupplyM
  let mkShareTy ty = mkTyConApp stc [mty, ty]
  let evsty = catMaybes $
              zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss tvs
  evs <- mapM freshDictId evsty
  lclEnv <- getLclEnv
  let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv

  allEvs <- (++evs) <$> liftIO (mapM replaceEv c)
  let cts = mkGivens ctloc allEvs
  let given' = given ++ cts
  (unlifted, _) <- liftIO (removeNondetShareable tcs mtc ftc stc (varType name))
  ty <- liftTypeTcM tcs argty unlifted
  let wrapLike = createWrapperLike ty tvs allEvs

  let (_, monotype) = splitInvisPiTysN (length tvs + length c)
                        (instantiateWith (map mkTyVarTy tvs) ty)
  (eqs', con) <- captureConstraints $ liftMonadicEquation
                    (if lcl then Nothing else Just (setVarType name monotype))
                    given' argty tcs eqs
  lvl <- getTcLevel
  env <- getLclEnv
  u <- getUniqueM
  ref1 <- newTcRef emptyEvBindMap
  ref2 <- newTcRef emptyVarSet
  let bindsVar = EvBindsVar u ref1 ref2

  let impls = mkImplications given' tvs lvl env bindsVar con
  let constraints = WC (listToBag given') impls emptyBag
  wx' <- mkWpLet . EvBinds <$> simplifyTop constraints
  zEnv <- emptyZonkEnv
  binds' <- snd <$> zonkTcEvBinds zEnv (TcEvBinds bindsVar)
  let wx = wx' <.> mkWpLet binds'

  let fullwrap = wrapLike <.> wx
  ticks' <- mapM (liftTick tcs argty) ticks
  let name' = setVarType name ty
  return ([FunBind fullwrap (L b name') eqs' ticks'], [])
  where
    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)
liftMonadicBinding lcl given argty' tcs _ (AbsBinds a b c d e f g)
  -- we do not want to lift dicts or record selectors or other system stuff here
  | all (noSystemNameOrRec . abe_poly) d = do
    -- create the dictionary variables
    stc <- getShareClassTycon
    sigVar <- if lcl then case argty' of { Just (TyVarTy v) -> return v; _ -> error "TODO"} else freshMonadTVar
    let argty =  mkTyVarTy sigVar
    mty <- flip mkTyConApp [argty] <$> getMonadTycon
    uss <- replicateM (length b) getUniqueSupplyM
    let mkShareTy ty = mkTyConApp stc [mty, ty]
    functorTyCon <- lookupTyCon functorClassName
    let functorSig = mkTyConApp functorTyCon [argty]
    let evsty = catMaybes (zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss b)
    evs <- mapM freshDictId (if lcl then evsty else functorSig:evsty)
    lclEnv <- getLclEnv
    let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv


    allEvs <- (++evs) <$> liftIO (mapM replaceEv c)
    let cts = mkGivens ctloc allEvs
    let given' = given ++ cts

    let b' = if lcl then b else sigVar:b
    (d', vs) <- unzip <$> mapM (liftEx b' allEvs mty (if lcl then Nothing else Just sigVar)) d
    let vs' = catMaybes vs

    -- lift inner bindings
    let bs = map unLoc (bagToList f)
    f' <- listToBag . map noLocA . concat
            <$> mapM (fmap fst . liftMonadicBinding lcl given' (Just argty) tcs [])
                (foldr (\(n, o, _) -> substitute n o) bs vs')

    -- lift any original evidence that is exported. This is only relevant
    -- for standalone AbsBinds that bind any class parent dictionary
    e' <- mapM (liftEvidence given' argty tcs)
              (filter isExportedEv (concatMap flattenEv e))
    vs'' <- mapM (\(v1,v2,v3) -> (,,v3)
                      <$> (setVarType v1 <$> liftTypeTcM tcs argty (varType v1))
                      <*> (setVarType v2 <$> liftTypeTcM tcs argty (varType v2))) vs'
    return ([AbsBinds a b' allEvs d' e' f' g], map (getLocFrom bs) vs'')
  where
    bindingVarMaybe :: HsBindLR GhcTc GhcTc -> Maybe (LocatedN Var)
    bindingVarMaybe (FunBind _ name _ _) = Just name
    bindingVarMaybe _                    = Nothing

    getLocFrom [] _ = error "Variable does not exist"
    getLocFrom (x:xs) (v1, v2, v3)
      | Just (L l name) <- bindingVarMaybe x,
        name == v3 = (v1, L l v2)
      | otherwise  = getLocFrom xs (v1, v2, v3)

    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)

    -- Basically do the same as in liftTopTypes, but this time for
    -- both the poly and mono type and for local bindings as well
    liftEx :: [Var] -> [Var] -> Type -> Maybe Var -> ABExport GhcTc -> TcM (ABExport GhcTc, Maybe (Var,Var,Var))
    liftEx vs evs mty sigVar' (ABE x v1 v2 _ p) = do
      env <- getGblEnv
      let aenv = tcg_ann_env env
      let anns = findAnns deserializeWithData aenv (NamedTarget (varName v1)) 
      -- change unique only for local decls, as only those are shared
      u <- if lcl then getUniqueM else return (varUnique v1)
      sigVar <- case sigVar' of
        Just v -> return v
        Nothing -> freshMonadTVar
      tys <- mapM (constraintTypeForAnn (occName sigVar)) anns
      printAny "sigty" tys
      let argty = mkTyVarTy sigVar
      -- lift types
      mtycon <- getMonadTycon
      ftycon <- getFunTycon
      stycon <- getShareClassTycon
      functorTyCon <- lookupTyCon functorClassName
      let functorSig = mkTyConApp functorTyCon [argty]

      -- We only want to introduce Shareable constraints for the type
      -- variables bound in this AbsBind, so we manually split off
      -- all type and evidence abstractions bound here.
      -- Then we can do the lifting and stuff.
      -- All of this is only done, when a lifting is even required.
      let v1ty = varType v1
      ty1 <- case splitTyConApp_maybe (snd (splitInvisPiTys v1ty)) of
        Just (tc, _) | tc == mtycon
          -> do
          (unlifted, _) <- liftIO (removeNondetShareable tcs mtycon ftycon stycon v1ty)
          mkPiTys undefined <$> liftTypeTcM tcs argty unlifted
        _ -> do
          let (bs1, t1) = splitInvisPiTys v1ty
          let bs = mapMaybe namedTyCoVarBinder_maybe bs1
          uss <- replicateM (length bs) getUniqueSupplyM
          let mkShareType t' = mkTyConApp stycon [mty, t']
              cons = catMaybes (zipWith (mkShareable mkShareType) uss bs)
          bs1' <- mapM (replacePiTyTcM tcs) bs1
          mkPiTys (if isNothing sigVar' then bs1' else Named (Bndr sigVar Inferred) : bs1')
            . flip (foldr mkInvisFunTyMany) (if isNothing sigVar' then cons else functorSig:cons)
            <$> liftTypeTcM tcs argty t1

      -- lift the mono type and create the new variables.
      ty2 <- liftTypeTcM tcs argty (varType v2)
      let v2' = setVarType v2 ty2
      let v1' = setVarType v1 ty1
      -- also (possibly) change unique for sharing
      let v1u = setVarUnique v1' u

       -- the type the function should have
      let targetTy = ty1
      -- the type the function has according to the absBinds
      let realTy = mkPiTys (map (Named . flip Bndr Inferred) vs ++ map (Anon InvisArg . Scaled Many . varType) evs) ty2


      -- The wrapper w deals with matching the impedence beteween the expected
      -- type of the exported function and the real type that is dictated by
      -- the type and evidence variables.
      -- See note [ABExport wrapper] in GHC.Hs.Binds.
      -- In addition to matching the type applications of the function,
      -- We also have to match the Shareable dictionaries
      -- that have been inserted.
      let (args, _) = splitInvisPiTys targetTy
      let toAbsts (Named (Bndr v _)) = return (v, WpTyLam v)
          toAbsts (Anon _ (Scaled _ ty)) = freshDictId ty >>= \v -> return (v, WpEvLam v)
      (vars, abstWraps) <- unzip <$> mapM toAbsts args
      let partitionBinder (Named _             , v) = Right v
          partitionBinder (Anon _ (Scaled _ ty), v) = Left (ty, v)
          (evs', vs') = partitionEithers $ foldr ((:) . partitionBinder) [] $ zip args vars
          abstWrapper = foldr (<.>) WpHole abstWraps

      -- For unused types, we can just apply GHC.Types.Any to them.
      -- For unused evidence, we cannot do this.
      -- Instead we create dummy evidence terms that have the right type
      -- by using unsafeCoerce.
      -- We know that the evidence is unused,
      -- because its type is Shareable Nondet Any.
      dfl <- getDynFlags
      let mkShareType t' = mkTyConApp stycon [mty, t']
          unsafeCoShare = Cast (mkIntExpr (targetPlatform dfl) 0)
            (mkUnivCo (PluginProv "unsafe") Representational
              intTy (mkShareType (anyTypeOfKind liftedTypeKind)))

      let fullwrap = abstWrapper <.> mkEvWrapFor (fst (splitInvisPiTys realTy)) unsafeCoShare evs' vs'
      return ( ABE x v1u v2' fullwrap p
             , Just (setVarUnique v1 u, v1, v2) )

    -- Do not lift any system stuff, except instance fun definitions ($c) and
    -- class default methods ($dm).
    noSystemNameOrRec v = case occNameString (occName v) of
      n | "$con2tag_" `isPrefixOf` n -> True
        | "$maxtag"   `isPrefixOf` n -> True
        | "$tag2con"  `isPrefixOf` n -> True
      '$':'c':_                      -> True
      '$':'d':'m':_                  -> True
      '$':xs@(_:_) | any isAlpha xs  -> False
      _                              -> not (isRecordSelector v)

    flattenEv (TcEvBinds _) = []
    flattenEv (EvBinds ebs) = bagToList ebs
    isExportedEv (EvBind v _ _) = any ((==v) . abe_mono) d
liftMonadicBinding _ _ _ tcs clsInsts bind@(AbsBinds _ _ _ d _ _ _)
  | all (isDictFun . abe_poly) d =
    maybe ([bind], []) ((,[]) . (:[]))
      <$> liftDictInstFun bind tcs clsInsts
  where
    isDictFun v = case occNameString (occName v) of
      '$':'f':_ -> True
      _         -> False
liftMonadicBinding _ _ _ tcs _ bind@(AbsBinds _ _ _ d _ _ _)
  | all (isRecordSelector . abe_poly) d =
    maybe ([bind], []) ((,[]) . (:[bind])) -- do not throw away the old selector
      <$> liftRecordSel tcs bind
liftMonadicBinding _ _ _ tcs _ (VarBind x1 name e1)
  -- This is the error binding for an unimplemented type class function.
  -- Anything like $c... = noMethodBindingError @ 'LiftedRep @ ty "..."#,
  | '$':'c':_ <- occNameString (occName name) = do
    let (wrap, e1') = case e1 of
                        L _ (XExpr (WrapExpr (HsWrap w e))) -> (w     , e)
                        L _ e                               -> (WpHole, e)
    case e1' of
      HsApp x2 (L l3 (XExpr (WrapExpr (HsWrap (WpCompose w1 w2) e2)))) e3 -> do
        mtycon <- getMonadTycon
        let mty = mkTyConApp mtycon [undefined]
        stycon <- getShareClassTycon
        -- Look at the number of abstractions in wrap.
        -- Those abstractions correspond to the vars bound in the instance head.
        -- Only for those we want Shareable.
        -- But only if the type is not lifted already.
        let numBinders = length (fst (collectHsWrapBinders wrap))
        let ty = varType name
        (ty', bndrs) <- case splitTyConApp_maybe (snd (splitInvisPiTys ty)) of
          Just (tc, _) | tc == mtycon
            -> (,[]) <$> liftIO (replaceTyconTy tcs ty)
          _ -> do
            let (bs1, ty1) = splitInvisPiTysN numBinders ty
                bs = mapMaybe namedTyCoVarBinder_maybe bs1
            uss <- replicateM (length bs) getUniqueSupplyM
            let mkShareType t' = mkTyConApp stycon [mty, t']
                cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
            bs1' <- mapM (replacePiTyTcM tcs) bs1
            (,cons) . mkPiTys bs1' . flip (foldr mkInvisFunTyMany) cons
              <$> liftTypeTcM tcs undefined ty1

        let name' = setVarType name ty'
        wrap' <- createAbstractionWrapperWith wrap bndrs
        w1' <- liftErrorWrapper tcs undefined w1
        w2' <- liftErrorWrapper tcs undefined w2
        let e1'' = HsApp x2 (L l3 (mkHsWrap (WpCompose w1' w2') e2)) e3
        return ([VarBind x1 name' (noLocA (mkHsWrap wrap' e1''))], [])
      _ -> panicAny "Unexpected layout of unimplemented method error expr" e1'
liftMonadicBinding _ _ _ _ _ a = return ([a], [])

-- The variables introduced here are guaranteed to be unused.
-- We just need to match the expected type.
createAbstractionWrapperWith :: HsWrapper -> [Type] -> TcM HsWrapper
createAbstractionWrapperWith w [] = return w
createAbstractionWrapperWith w (ty : tys) = do
  v <- freshDictId ty
  createAbstractionWrapperWith (w <.> WpEvLam v) tys

liftEvidence :: [Ct] -> Type -> TyConMap -> EvBind -> TcM TcEvBinds
liftEvidence given argty tcs (EvBind v _ _) = do
  -- Re-create constraints with the lifted constraint type
  -- This is only used for class parent dictionaries,
  -- so this is never a coercion that needs to be solved
  ty <- liftTypeTcM tcs argty (varType v)
  loc <- getCtLocM (OccurrenceOf (varName v)) Nothing
  let dst = EvVarDest (setVarType v ty)
  let cts = [CNonCanonical (CtWanted ty dst WDeriv loc)]
  -- solve them
  EvBinds <$> simplifyTop (WC (listToBag (cts ++ given)) emptyBag emptyBag)

liftLocalBinds :: [Ct] -> Type -> TyConMap -> HsLocalBinds GhcTc
               -> TcM (HsLocalBinds GhcTc, [(Var, LocatedN Var)])
liftLocalBinds given argty tcs (HsValBinds x b) = do
  (b', vs) <- liftValBinds given argty tcs b
  return (HsValBinds x b', vs)
liftLocalBinds _ _ _ b@(HsIPBinds _ _) = do
  reportError (mkMsgEnvelope noSrcSpan neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return (b, [])
liftLocalBinds _ _ _ b = return (b, [])

liftValBinds :: [Ct] -> Type -> TyConMap -> HsValBindsLR GhcTc GhcTc
             -> TcM (HsValBindsLR GhcTc GhcTc, [(Var, LocatedN Var)])
liftValBinds _ _ _ bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
liftValBinds given argty tcs (XValBindsLR (NValBinds bs _)) = do
  (bs', vss) <- unzip <$> mapM liftNV bs
  return (XValBindsLR (NValBinds bs' []), concat vss)
  where
    liftNV :: (RecFlag, LHsBinds GhcTc)
           -> TcM ((RecFlag, LHsBinds GhcTc), [(Var, LocatedN Var)])
    liftNV (rf, b) = do
      let bs1 = map unLoc (bagToList b)
      (bs2, vss) <- first (map noLocA . concat) . unzip <$>
        mapM (liftMonadicBinding True given (Just argty) tcs []) bs1
      return ((rf, listToBag bs2), concat vss)

liftMonadicEquation :: Maybe Var -> [Ct] -> Type -> TyConMap
                    -> MatchGroup GhcTc (LHsExpr GhcTc)
                    -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftMonadicEquation mv given argty tcs (MG a (L b alts) c) = do
  a'@(MatchGroupTc _ res) <- liftMGTc tcs argty a
  alts' <- mapM (liftMonadicAlt mv given argty tcs res) alts
  return (MG a' (L b alts') c)

liftMGTc :: TyConMap -> Type -> MatchGroupTc -> TcM MatchGroupTc
liftMGTc tcs argty (MatchGroupTc args res) = do
  res' <- liftTypeTcM tcs argty res
  args' <- mapM (\(Scaled m ty) -> Scaled m <$> liftTypeTcM tcs argty ty) args
  return (MatchGroupTc args' res')

liftMonadicAlt :: Maybe Var -> [Ct] -> Type -> TyConMap -> Type
               -> LMatch GhcTc (LHsExpr GhcTc)
               -> TcM (LMatch GhcTc (LHsExpr GhcTc))
liftMonadicAlt mv given argty tcs resty (L a (Match b c d rhs)) = do
  (d', s) <- unzip <$> mapM (liftPattern tcs argty) d
  rhs' <- liftMonadicRhs mv (concat s) given argty tcs resty rhs
  return (L a (Match b c d' rhs'))

liftMonadicRhs :: Maybe Var -> [(Var, LocatedN Var)] -> [Ct] -> Type -> TyConMap
               -> Type -> GRHSs GhcTc (LHsExpr GhcTc)
               -> TcM (GRHSs GhcTc (LHsExpr GhcTc))
liftMonadicRhs mv s given argty tcs resty (GRHSs a grhs b) = do
  grhs' <- mapM (liftMonadicGRhs mv s given argty tcs resty) grhs
  return (GRHSs a grhs' b)

liftMonadicGRhs :: Maybe Var -> [(Var, LocatedN Var)] -> [Ct] -> Type -> TyConMap
                -> Type -> LGRHS GhcTc (LHsExpr GhcTc)
                -> TcM (LGRHS GhcTc (LHsExpr GhcTc))
liftMonadicGRhs mv s given argty tcs bdyty (L a (GRHS b c body)) = do
  body' <- liftMonadicExpr given argty tcs body
  body'' <- shareVars tcs argty s given body' bdyty
  L a . GRHS b c <$> shareTopLevel mv body''

liftMonadicExpr :: [Ct] -> Type -> TyConMap -> LHsExpr GhcTc
                -> TcM (LHsExpr GhcTc)
liftMonadicExpr given argty tcs (L _ (HsVar _ (L _ v))) = do
  dtt <- tcLookupId =<< lookupOrig gHC_PRIM ( mkVarOcc "dataToTag#" )
  liftVarWithWrapper given argty tcs WpHole v (varUnique dtt)
liftMonadicExpr given argty tcs (L _ (XExpr (WrapExpr (HsWrap w (HsVar _ (L _ v)))))) = do
  dtt <- tcLookupId =<< lookupOrig gHC_PRIM ( mkVarOcc "dataToTag#" )
  liftVarWithWrapper given argty tcs w v (varUnique dtt)
liftMonadicExpr _    argty _   e@(L _ (HsLit _ (HsIntPrim _ _))) = do
  conE <- liftQ [| I# |]
  let conty = mkVisFunTyMany intPrimTy intTy
  lit <- mkApp (mkNewAny conE) conty [e]
  mkApp (mkNewReturnTh argty) intTy [noLocA (HsPar EpAnnNotUsed lit)]
liftMonadicExpr _    argty tcs e@(L _ HsLit{}) = do
  ty <- getTypeOrPanic e -- ok
  lifted <- mkApp (mkNewReturnTh argty) ty [e]
  ty' <- liftInnerTyTcM tcs argty ty
  res <- mkApp (mkNewLiftETh argty ty) ty' [lifted]
  return $ noLocA $ HsPar EpAnnNotUsed res
liftMonadicExpr given argty tcs (L l (HsOverLit _ lit)) =
  case ol_witness lit of
    -- if this is geniunely a Double or Float, just wrap it with return
    e@(HsApp _ (L _ (HsConLikeOut _ (RealDataCon dc))) _)
      | dc == doubleDataCon || dc == floatDataCon -> do
        ty <- getTypeOrPanic (noLocA e) -- ok
        mkApp (mkNewReturnTh argty) ty [noLocA e]
    -- otherwise, just lift the witness
    _ -> liftMonadicExpr given argty tcs (L l (ol_witness lit))
liftMonadicExpr given argty tcs (L l (HsLam _ mg)) =
  liftLambda given argty tcs l Nothing mg
liftMonadicExpr given argty tcs (L l (HsLamCase _ mg)) =
  liftLambda given argty tcs l Nothing mg
liftMonadicExpr _ argty tcs (L _ (HsConLikeOut _ (RealDataCon c)))
  | c == intDataCon = do
    idExp <- liftQ [| return id |]
    mtycon <- getMonadTycon
    let ty = mkTyConApp mtycon [mkTyConApp mtycon [intTy] `mkVisFunTyMany`
                                mkTyConApp mtycon [intTy]]
    mkApp (mkNewAny idExp) ty []
  | otherwise = do
    c' <- liftIO (getLiftedCon c tcs)
    let tys = dataConOrigArgTys c'
    let stricts = dataConImplBangs c'
    e <- fst <$> mkConLam tcs argty Nothing c' (zip tys stricts) []
    return $ noLocA $ HsPar EpAnnNotUsed e
liftMonadicExpr _ argty tcs (L _ (XExpr (WrapExpr (HsWrap w (HsConLikeOut _ (RealDataCon c))))))
  | c == intDataCon = do
    idExp <- liftQ [| return id |]
    mtycon <- getMonadTycon
    let ty = mkTyConApp mtycon [mkTyConApp mtycon [intTy] `mkVisFunTyMany`
                                mkTyConApp mtycon [intTy]]
    mkApp (mkNewAny idExp) ty []
  | otherwise = do
    c' <- liftIO (getLiftedCon c tcs)
    w' <- liftWrapperTcM True argty tcs w
    let (apps, absts) = collectTyApps w'
        realApps = drop (length absts) apps
    mty <- flip mkTyConApp [argty] <$> getMonadTycon
    let tys = conLikeInstOrigArgTys (RealDataCon c') (mty : realApps)
    let stricts = dataConImplBangs c'
    e <- fst <$> mkConLam tcs argty (Just w') c' (zip tys stricts) []
    return $ noLocA $ HsPar EpAnnNotUsed e
liftMonadicExpr given argty tcs (L _ (OpApp _ e1 op e2)) = do
  -- e1 `op` e2
  -- -> (op `appFL` e1) `appFL` e2
  opty1 <- getTypeOrPanic op >>= liftTypeTcM tcs argty -- ok
  e1' <- liftMonadicExpr given argty tcs e1
  op' <- liftMonadicExpr given argty tcs op
  e2' <- liftMonadicExpr given argty tcs e2
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let mty = mkTyConApp mtc [argty]
  let (argty1, opty2) = splitMyFunTy mty ftc $ bindingType opty1
  let (argty2, _    ) = splitMyFunTy mty ftc $ bindingType opty2
  e1'' <- mkFuncApp given op' argty opty1 e1' argty1
  let bracketed = noLocA (HsPar EpAnnNotUsed e1'')
  e2'' <- mkFuncApp given bracketed argty opty2 e2' argty2
  return $ noLocA $ HsPar EpAnnNotUsed e2''
liftMonadicExpr given argty tcs (L _ (HsApp _ fn ex)) = do
  -- e1 e2
  -- -> e1 `appFL` e2
  fn' <- liftMonadicExpr given argty tcs fn
  ex' <- liftMonadicExpr given argty tcs ex
  funty <- getTypeOrPanic fn >>= liftTypeTcM tcs argty
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let mty = mkTyConApp mtc [argty]
  let (fargty, _) = splitMyFunTy mty ftc $ bindingType funty
  res <- mkFuncApp given fn' argty funty ex' fargty
  return $ noLocA $ HsPar EpAnnNotUsed res
liftMonadicExpr given argty tcs (L _ (HsAppType _ e _)) =
  liftMonadicExpr given argty tcs e
liftMonadicExpr given argty tcs (L l (NegApp _ e (SyntaxExprTc n ws w))) =
  liftMonadicExpr given argty tcs (L l (mkHsWrap w
    (HsApp EpAnnNotUsed (noLocA n) (fmap (mkHsWrap (head ws)) e))))
liftMonadicExpr _ _ _ (L _ (NegApp _ _ NoSyntaxExprTc)) = undefined
liftMonadicExpr given argty tcs (L l (HsPar x e)) =
  L l . HsPar x <$> liftMonadicExpr given argty tcs e
liftMonadicExpr _ _ _ e@(L _ (SectionL _ _ _)) = do
  panicAny "Sections should have been desugared by GHC already" e
liftMonadicExpr _ _ _ e@(L _ (SectionR _ _ _)) =
  panicAny "Sections should have been desugared by GHC already" e
liftMonadicExpr given argty tcs (L _ (ExplicitTuple _ args b)) =
  liftExplicitTuple given argty tcs args b
liftMonadicExpr _    _  _ e@(L _ ExplicitSum {}) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given argty tcs (L l (HsCase _ scr br)) = do
  br'@(MG (MatchGroupTc _ ty2) _ _) <- liftMonadicEquation Nothing given argty tcs br
  scr' <- liftMonadicExpr given argty tcs scr
  ty1 <- getTypeOrPanic scr >>= liftTypeTcM tcs argty -- ok
  let cse = L l $ HsLamCase EpAnnNotUsed br'
  mkBind scr' argty ty1 (noLocA $ HsPar EpAnnNotUsed cse) ty2
liftMonadicExpr given argty tcs (L l (HsIf _ e1 e2 e3)) = do
  -- if e1 then e2 else e3
  -- -> e1 >>= \case { True -> e2; _ -> e3 }
  e1' <- liftMonadicExpr given argty tcs e1
  e2' <- liftMonadicExpr given argty tcs e2
  e3' <- liftMonadicExpr given argty tcs e3
  ty1' <- getTypeOrPanic e1 >>= liftTypeTcM tcs argty -- ok
  ty2' <- getTypeOrPanic e2 >>= liftTypeTcM tcs argty -- ok
  let ty1 = bindingType ty1'
  v <- noLocA <$> freshVar (Scaled Many ty1)
  let ife = HsIf noExtField (noLocA (HsVar noExtField v)) e2' e3'
  let alt = mkSimpleAlt LambdaExpr (noLocA ife) [noLocA (VarPat noExtField v)]
  let mgtc = MatchGroupTc [Scaled Many ty1] ty2'
  let mg = MG mgtc (noLocA [noLocA alt]) Generated
  mkBind e1' argty ty1' (noLocA $ HsPar EpAnnNotUsed $ L l $ HsLam noExtField mg) ty2'
liftMonadicExpr _ _ _ e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
liftMonadicExpr given argty tcs (L l (HsLet x bs e)) = do
  -- Lift local binds first, so that they end up in the type environment.
  (bs', vs) <- liftLocalBinds given argty tcs bs
  e' <- liftMonadicExpr given argty tcs e
  ety <- getTypeOrPanic e >>= liftTypeTcM tcs argty -- ok
  e'' <- shareVars tcs argty vs given e' ety
  return (L l (HsLet x bs' e''))
liftMonadicExpr given argty tcs (L l1 (HsDo x ctxt (L l2 stmts))) = do
  x' <- liftTypeTcM tcs x argty
  -- Because ListComp are not overloadable,
  -- we have to change them to MonadComp.
  let ctxtSwitch | ListComp <- ctxt = True
                 | otherwise        = False
  let ctxt' | ctxtSwitch = MonadComp
            | otherwise  = ctxt
  stmts' <- liftMonadicStmts ctxt' ctxtSwitch x' given argty tcs stmts
  return (L l1 (HsDo x' ctxt' (L l2 stmts')))
liftMonadicExpr given argty tcs (L _ (ExplicitList ty es)) = do
  -- [e1, ..., en]
  -- -> return (Cons e1 (return (Cons ... (return (Cons en (return Nil))))))
  em <- mkEmptyList ty tcs
  liftedTy <- liftInnerTyTcM tcs argty (mkListTy ty) -- ok
  nil <- mkApp (mkNewReturnTh argty) liftedTy [em]
  if null es
    then return nil
    else do
      es' <- mapM (liftMonadicExpr given argty tcs) es
      cons <- mkConsList ty tcs
      let mkCons e1 e2 = let e' = mkHsApp (mkHsApp cons e1) e2
                         in mkApp (mkNewReturnTh argty) liftedTy [e']
      foldrM mkCons nil es'
liftMonadicExpr given argty tcs (L l1 (RecordCon ce (L l2 (RealDataCon c)) fs)) = do
  c' <- liftIO (getLiftedCon c tcs)
  ce' <- liftConExpr tcs argty c' ce
  fs' <- liftMonadicRecFields given argty tcs fs
  let e = L l1 (RecordCon ce' (L l2 (RealDataCon c')) fs')
  if isNewTyCon (dataConTyCon c')
    then return e
    else getTypeOrPanic e >>= flip (mkApp (mkNewReturnTh argty)) [e] -- ok
liftMonadicExpr _ _ _ e@(L _ (RecordCon _ (L _ (PatSynCon _)) _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Pattern synonyms are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given argty tcs (L l (RecordUpd rtc e fs)) = do
  rtc'@(RecordUpdTc (c:_) inty outty _)  <- liftMonadicRecordUpd argty tcs rtc
  e' <- liftMonadicExpr given argty tcs e
  fs' <- either (fmap Left . mapM (liftMonadicRecordUpdField given argty tcs))
                (fmap Right . mapM  (liftMonadicRecordProjField given argty tcs))
                fs
  let vty = conLikeResTy c inty
  v <- noLocA <$> freshVar (Scaled Many vty)
  let upd = L l (RecordUpd rtc' (noLocA (HsVar noExtField v)) fs')
  let updTy = conLikeResTy c outty
  let updLam = mkLam v (Scaled Many vty) upd updTy
  mkApp (mkNewFmapTh argty vty) updTy [updLam, e']
liftMonadicExpr given argty tcs (L _ (ExprWithTySig _ e _)) =
  liftMonadicExpr given argty tcs e
liftMonadicExpr given argty tcs (L _ (ArithSeq x Nothing i)) =
  liftMonadicExpr given argty tcs (foldl mkHsApp (noLocA x) (arithSeqArgs i))
liftMonadicExpr _ _ _ e@(L _ (ArithSeq _ (Just _) _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given argty tcs (L l (HsPragE x (HsPragSCC a b c) e)) =
  L l . HsPragE x (HsPragSCC a b c) <$> liftMonadicExpr given argty tcs e
liftMonadicExpr _ _ _ e@(L _ (HsBracket _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ _ e@(L _ (HsSpliceE _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ _ e@(L _ (HsTcBracketOut _ _ _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ _ e@(L _ (HsProc _ _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Arrow notation is not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given argty tcs (L l (HsStatic x e)) =
  L l . HsStatic x <$> liftMonadicExpr given argty tcs e
liftMonadicExpr given argty tcs (L l (HsTick a tick e)) = do
  (L l .) . HsTick a <$> liftTick tcs argty tick <*> liftMonadicExpr given argty tcs e
liftMonadicExpr given argty tcs (L l (HsBinTick a b c e)) =
  L l . HsBinTick a b c <$> liftMonadicExpr given argty tcs e
liftMonadicExpr given argty tcs (L l (XExpr (WrapExpr (HsWrap w e)))) = do
  e' <- unLoc <$> liftMonadicExpr given argty tcs (L l e)
  w' <- liftWrapperTcM True argty tcs w
  return (L l (mkHsWrap w' e'))
liftMonadicExpr _ _ _ (L _ (HsUnboundVar _ _)) = undefined
liftMonadicExpr _ _ _ (L _ (HsRecFld _ _)) = undefined
liftMonadicExpr _ _ _ (L _ (HsOverLabel _ _)) = undefined
liftMonadicExpr _ _ _ (L _ (HsIPVar _ _)) = undefined
liftMonadicExpr _ _ _ (L _ (HsRnBracketOut _ _ _)) = undefined
liftMonadicExpr _ _ _ (L _ (HsConLikeOut _ _)) = undefined
liftMonadicExpr _ _ _ (L _ (XExpr (ExpansionExpr _))) = undefined
liftMonadicExpr _ _ _ (L (SrcSpanAnn _ _) (HsGetField _ _ _)) = undefined
liftMonadicExpr _ _ _ (L (SrcSpanAnn _ _) (HsProjection _ _)) = undefined


liftMonadicStmts :: HsStmtContext GhcRn -> Bool -> Type -> [Ct] -> Type -> TyConMap
                 -> [ExprLStmt GhcTc] -> TcM [ExprLStmt GhcTc]
liftMonadicStmts _ _ _ _ _ _ [] = return []
liftMonadicStmts ctxt ctxtSwitch ty given argty tcs (s:ss) = do
  (s', vs) <- liftMonadicStmt s
  ss' <- liftMonadicStmts ctxt ctxtSwitch ty given argty tcs ss
  if null vs
    then return (s':ss')
    else do
      e <- shareVars tcs argty vs given (noLocA (HsDo ty ctxt (noLocA ss'))) ty
      return [s', noLocA (LastStmt noExtField e Nothing NoSyntaxExprTc)]
  where
    liftMonadicStmt :: ExprLStmt GhcTc
                    -> TcM (ExprLStmt GhcTc, [(Var, LocatedN Var)])
    liftMonadicStmt (L l (LastStmt x e a r)) = do
      e' <- liftMonadicExpr given argty tcs e
      r' <- if synExprExists r
              then trans1 r
              else return r
      return (L l (LastStmt x e' a r'), [])
    liftMonadicStmt (L l (BindStmt (XBindStmtTc b x m f) p e)) = do
      -- p is definitely just a varPat and f is NoSyntaxExprTc or Nothing
      (p', vs) <- liftPattern tcs argty p
      e' <- liftMonadicExpr given argty tcs e
      x' <- liftTypeTcM tcs argty x
      b' <- transBind b
      return (L l (BindStmt (XBindStmtTc b' x' m f) p' e'), vs)
    liftMonadicStmt (L _ (ApplicativeStmt _ _ _)) = do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Applicative do-notation is not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l (BodyStmt x e se g)) = do
      x' <- liftTypeTcM tcs argty x
      e' <- liftMonadicExpr given argty tcs e
      se' <- trans2 se
      g' <- if synExprExists g
              then trans1 g
              else return g
      return (L l (BodyStmt x' e' se' g'), [])
    liftMonadicStmt (L l (LetStmt x bs)) = do
      (bs', vs) <- liftLocalBinds given argty tcs bs
      return (L l (LetStmt x bs'), vs)
    liftMonadicStmt (L _ (ParStmt _ _ _ _)) = do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L _ (TransStmt _ _ _ _ _ _ _ _ _)) = do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L _ (RecStmt _ _ _ _ _ _ _)) = do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Recursive do-notation is not supported by the plugin")
      failIfErrsM
      return (s, [])


    synExprExists NoSyntaxExprTc = False
    synExprExists _              = True

    trans1 (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given argty tcs (noLocA (mkHsWrap w e))
      e1ty <- getTypeOrPanic (noLocA e) >>= liftTypeTcM tcs argty -- ok
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let mty = mkTyConApp mtc [argty]
      let (ty1, ty2) = splitMyFunTy mty ftc (bindingType e1ty)
      e2 <- mkApp (mkNewApply1 argty (bindingType ty1)) (bindingType ty2) [e1]
      ws' <- mapM (liftWrapperTcM True argty tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    trans1 NoSyntaxExprTc = return NoSyntaxExprTc

    transBind (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given argty tcs (noLocA (mkHsWrap w e))
      e1ty <- getTypeOrPanic (noLocA e) >>= liftTypeTcM tcs argty -- ok
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let mty = mkTyConApp mtc [argty]
      let (ty1, restty) = splitMyFunTy mty ftc (bindingType e1ty)
      let (ty2, ty3) = splitMyFunTy mty ftc (bindingType restty)
      e2 <- mkApp (mkNewApply2Unlifted argty (bindingType ty1) (bindingType ty2))
                  (bindingType ty3) [e1]
      ws' <- mapM (liftWrapperTcM True argty tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    transBind NoSyntaxExprTc = return NoSyntaxExprTc

    trans2 (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given argty tcs (noLocA (mkHsWrap w e))
      e1ty <- getTypeOrPanic (noLocA e) >>= liftTypeTcM tcs argty -- ok
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let mty = mkTyConApp mtc [argty]
      let (ty1, restty) = splitMyFunTy mty ftc (bindingType e1ty)
      let (ty2, ty3) = splitMyFunTy mty ftc (bindingType restty)
      e2 <- mkApp (mkNewApply2 argty (bindingType ty1) (bindingType ty2))
                  (bindingType ty3) [e1]
      ws' <- mapM (liftWrapperTcM True argty tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    trans2 NoSyntaxExprTc = return NoSyntaxExprTc

liftLambda :: [Ct] -> Type -> TyConMap -> SrcSpanAnnA
           -> Maybe Type -> MatchGroup GhcTc (LHsExpr GhcTc)
           -> TcM (LHsExpr GhcTc)
liftLambda given argty tcs l _ mg = do
  mg'@(MG (MatchGroupTc [Scaled _ arg] res) _ _)
    <- liftMonadicEquation Nothing given argty tcs mg
  let e = L l (HsLam noExtField mg')
  mkApp (mkNewReturnFunTh argty arg) res [noLocA (HsPar EpAnnNotUsed e)]

-- We need to pay special attention to a lot of different kinds of variables.
-- Most of those kinds can be treated sinilarly (see below), but for
-- record selectors, we need a different approach.
liftVarWithWrapper :: [Ct] -> Type -> TyConMap -> HsWrapper -> Var -> Unique
                   -> TcM (LHsExpr GhcTc)
liftVarWithWrapper given argty tcs w v dttKey
  | varUnique v == coerceKey,
    ([_,ty1,ty2], _) <- collectTyApps w = transCoerce tcs given ty1 ty2
  | varUnique v == tagToEnumKey = do
    let appliedType = head $ fst $ collectTyApps w
    liftedType <- liftTypeTcM tcs argty appliedType
    -- tagToEnum :: Int# -> tyApp in w
    -- returnFunc (\flint ndint -> ndint >>= \(I# i) -> liftE (tagToEnum @w i)))
    lam <- liftQ [| \ttenum ndint -> ndint >>=
                    (\(I# i) -> liftE (return (ttenum i))) |]
    mtycon <- getMonadTycon
    let fargty = mkTyConApp mtycon [intTy]
    let resty = liftedType
    let ety = (intPrimTy `mkVisFunTyMany` appliedType)
                `mkVisFunTyMany` fargty `mkVisFunTyMany` resty
    let tte = noLocA (mkHsWrap w (HsVar noExtField (noLocA v)))
    e <- noLocA . HsPar EpAnnNotUsed <$> mkApp (mkNewAny lam) ety [tte]
    mkApp (mkNewReturnFunTh argty fargty) resty [e]
  | varUnique v == dttKey = do
    let appliedType = head $ fst $ collectTyApps w
    liftedType <- liftTypeTcM tcs argty appliedType
    -- dataToTagKey :: tyApp in w -> Int#
    -- returnFunc (\x -> x >>= \x' -> return (I# (dataToTagKey @w x')))
    lam <- liftQ [| \dtt x -> x >>= (\x' -> return (I# (dtt x'))) |]
    mtycon <- getMonadTycon
    w' <- liftWrapperTcM True argty tcs w
    let fargty = liftedType
    let resty = mkTyConApp mtycon [intTy]
    let ety = (bindingType liftedType `mkVisFunTyMany` intPrimTy)
               `mkVisFunTyMany` fargty `mkVisFunTyMany` resty
    let dtt = noLocA (mkHsWrap w' (HsVar noExtField (noLocA v)))
    e <- noLocA . HsPar EpAnnNotUsed <$> mkApp (mkNewAny lam) ety [dtt]
    mkApp (mkNewReturnFunTh argty fargty) resty [e]
  | isRecordSelector v = do
    -- lift type
    mtc <- getMonadTycon
    let mty = mkTyConApp mtc [argty]
    stc <- getShareClassTycon
    ftc <- getFunTycon
    w' <- liftWrapperTcM True argty tcs w
    us <- getUniqueSupplyM

    let (apps, abstrs) = collectTyApps w'
    let realApps = drop (length abstrs) apps
    let (arg, res) = splitMyFunTy mty ftc (instantiateWith realApps (varType v))

    let p = sel_tycon (idDetails v)
    v' <- liftIO (getLiftedRecSel stc ftc mty us tcs p v)

    let vExpr = noLocA (mkHsWrap w' (HsVar noExtField (noLocA v')))
    e <- case p of
      RecSelData tc
        -- translate any newtype  record selector "sel" to "return (fmap sel)"
        | isNewTyCon tc -> mkApp (mkNewFmapTh argty arg) res [vExpr]
        -- translate any datatype record selector "sel" to "return (>>= sel)"
      _                 -> do
        thE <- liftQ [| flip (>>=) |]
        bind <- mkApp (mkNewBindTh argty arg) (bindingType res) []
        bindTy <- getTypeOrPanic bind
        let thEty = bindTy -- TODO
        mkApp (mkNewAny thE) thEty [bind]
    ety <- getTypeOrPanic e -- ok
    mkApp (mkNewReturnTh argty) ety [noLocA (HsPar EpAnnNotUsed e)]
  | otherwise          = do
  -- lift type
  w' <- liftWrapperTcM True argty tcs w
  stc <- getShareClassTycon
  mtc <- getMonadTycon
  ftc <- getFunTycon
  (unlifted, _) <- liftIO (removeNondetShareable tcs mtc ftc stc (varType v))
  ty' <- liftTypeTcM tcs argty unlifted

  let (apps, absts) = collectTyApps w'
  let abstsWrap = foldr ((<.>) . WpTyLam) WpHole absts

  -- 1. If it is a typeclass operation, we re-create it from scratch to get
  --    the unfolding information right.
  -- 2. If it is a default method,
  --    we have to set the correct type and
  --    switch to the correct default method.
  --    For a non-builtin default method,
  --    we have to make some adjustments to the lifting.
  -- 3. If it is a LclId, just use the lifted type.
  -- 4. If it is one of a specific set of methods from the Prelude
  --    (due to deriving), we have to switch to the correct method.
  --    This falls back to just returning the current identifier,
  --    If no replacement function is found.
  let mv' | ClassOpId cls <- idDetails v = do
            cls' <- liftIO (getLiftedClass cls tcs)
            -- lookup the corresponding new name for the selector
            let sels = map idName (classAllSelIds cls)
                sels' = map idName (classAllSelIds cls')
            case find ((== varName v) . fst) (zip sels [0..]) of
              Just (_, idx) -> return (mkDictSelId (sels' !! idx) cls')
              Nothing -> panicAny "Class mismatch for built-in class" cls'
          | '$':'d':'m':_ <- occNameString (occName v) = do
            -- Split the type to get the class that this is the default method
            -- for, and look up the new version of that class.
            let tc = tyConAppTyCon (funArgTy (snd (splitForAllTyCoVars (varType v))))
            tc' <- liftIO (lookupTyConMap GetNew tcs tc)
            if tc == tc' -- if they are equal, this is NOT a built-in class.
              then case tyConClass_maybe tc of
                Nothing  -> panicAny "Expected a class, but recieved" tc
                Just cls -> setVarType v <$> liftDefaultType tcs cls argty unlifted
              -- Otherwise, look up the replacement of the default method.
              else
                lookupDefaultReplacement tc tc' (varName v)
          | isLocalId v =
            return (setVarType v ty')
          | otherwise = do
            mbv <- lookupWiredInFunc v
            case mbv of
              Nothing -> return (setVarType v ty')
              Just v' -> return v'
  v' <- mv'

  functorTyCon <- lookupTyCon functorClassName
  let functorSig = mkTyConApp functorTyCon [argty]

  let monotype = instantiateWith apps (varType v')
      getPred (Anon _ (Scaled _ t))
        | all (\cv -> countVarOcc cv t == 0) absts
                = Just t
      getPred _ = Nothing
      preds = if isExternalName (varName v) then functorSig : mapMaybe getPred (fst (splitInvisPiTys monotype)) else mapMaybe getPred (fst (splitInvisPiTys monotype))

  -- construct wanted constraints
  wanted <- newWanteds (OccurrenceOf (varName v')) preds
  let evvars = mapMaybe (getDest . ctev_dest) wanted
      getDest (EvVarDest d) = Just d
      getDest _             = Nothing
      cts = map CNonCanonical wanted

  lvl <- getTcLevel
  env <- getLclEnv
  u <- getUniqueM
  ref1 <- newTcRef emptyEvBindMap
  ref2 <- newTcRef emptyVarSet
  let bindsVar = EvBindsVar u ref1 ref2
  -- filter is just here to be sure
  evidence <- do
    let givenVars = map (ctEvEvId . cc_ev) $ filter isGivenCt given
    let i = Implic lvl absts UnkSkol givenVars MaybeGivenEqs False env
              (WC (listToBag cts) emptyBag emptyBag) bindsVar emptyVarSet
              emptyVarSet IC_Unsolved
    emitImplication i
    return $ mkWpLet (TcEvBinds bindsVar)

  let sigVar = case argty of {TyVarTy tv -> tv; _ -> error "TODO"}
  let finalTy = if isExternalName (varName v)
          then let (vs, ty) = splitForAllTyCoVars (varType v')
               in mkPiTys ([Named (Bndr sigVar Inferred)] ++ map (Named . flip Bndr Inferred) vs ++ [Anon InvisArg (Scaled Many functorSig)]) ty
          else (varType v')

  -- create the new wrapper, with the new dicts and the type applications
  let wdict = createWrapperFor finalTy (if isExternalName (varName v) then argty:apps else apps) evvars
  let wall = abstsWrap <.> (evidence <.> wdict)
  return $ noLocA $ mkHsWrap wall $ HsVar noExtField $ noLocA (setVarType v' finalTy)

-- (,b,) = return $ \x1 -> return $ \x2 -> return (x1, b, x2)
liftExplicitTuple :: [Ct] -> Type -> TyConMap -> [HsTupArg GhcTc]
                  -> Boxity -> TcM (LHsExpr GhcTc)
liftExplicitTuple given argty tcs args b = do
  resty <- getTypeOrPanic (noLocA $ ExplicitTuple noExtField args b) -- ok
  lifted <- liftTypeTcM tcs argty resty
  liftExplicitTuple' (bindingType lifted) [] WpHole args
  where
    liftExplicitTuple' :: Type -> [LHsExpr GhcTc] -> HsWrapper
                       -> [HsTupArg GhcTc] -> TcM (LHsExpr GhcTc)
    liftExplicitTuple' resty col w (Present _ e : xs) = do
      e' <- liftMonadicExpr given argty tcs e
      ty <- getTypeOrPanic e >>= liftTypeTcM tcs argty -- ok
      let w' = WpTyApp (bindingType ty) <.> w
      liftExplicitTuple' resty (e' : col) w' xs
    liftExplicitTuple' resty col w (Missing (Scaled m ty) : xs) = do
      ty' <- liftTypeTcM tcs argty ty
      v <- noLocA <$> freshVar (Scaled m ty')
      let arg = noLocA (HsVar noExtField v)
      let w' = WpTyApp (bindingType ty') <.> w
      ftc <- getFunTycon
      mtc <- getMonadTycon
      let mty = mkTyConApp mtc [argty]
      let (_, resty') = splitMyFunTy mty ftc resty
      inner <- liftExplicitTuple' (bindingType resty') (arg:col) w' xs
      let lam = mkLam v (Scaled m ty') inner resty'
      mkApp (mkNewReturnFunTh argty ty') resty' [lam]
    liftExplicitTuple' resty col w [] = do
      let exprArgs = reverse col
      dc <- liftIO (getLiftedCon (tupleDataCon b (length exprArgs)) tcs)
      let ce = mkHsWrap w (HsConLikeOut noExtField (RealDataCon dc))
      mkApp (mkNewReturnTh argty) resty
        [foldl mkHsApp (noLocA ce) exprArgs]

-- This is for RecordConstructors only.
-- We are interested in lifting the (potential wrapper)
-- and we want to replace the HsConLike with the lifted constructor version.
-- HsConLike is the only sensible option for this PostTcExpr for Haskell2010.
liftConExpr :: TyConMap -> Type -> DataCon -> PostTcExpr -> TcM PostTcExpr
liftConExpr tcs argty dc (XExpr (WrapExpr (HsWrap w _))) = do
    w' <- liftWrapperTcM True argty tcs w
    return (mkHsWrap w' (HsConLikeOut noExtField (RealDataCon dc)))
liftConExpr _ _ dc _ = return (HsConLikeOut noExtField (RealDataCon dc))

liftMonadicRecFields :: [Ct] -> Type -> TyConMap
                     -> HsRecordBinds GhcTc
                     -> TcM (HsRecordBinds GhcTc)
liftMonadicRecFields given argty tcs (HsRecFields flds dotdot) =
  flip HsRecFields dotdot <$> mapM (liftMonadicRecField given argty tcs) flds

liftMonadicRecordUpd :: Type -> TyConMap -> RecordUpdTc -> TcM RecordUpdTc
liftMonadicRecordUpd argty tcs (RecordUpdTc cs intys outtys wrap) = do
  RecordUpdTc <$> mapM conLike cs
              <*> mapM (liftInnerTyTcM tcs argty) intys
              <*> mapM (liftInnerTyTcM tcs argty) outtys
              <*> liftWrapperTcM True argty tcs wrap
  where
    conLike (RealDataCon c) = RealDataCon <$> liftIO (getLiftedCon c tcs)
    conLike p@(PatSynCon _) = do
      reportError (mkMsgEnvelope noSrcSpan neverQualify
        "Pattern synonyms are not supported by the plugin")
      failIfErrsM
      return p

liftMonadicRecordUpdField :: [Ct] -> Type -> TyConMap -> LHsRecUpdField GhcTc
                          -> TcM (LHsRecUpdField GhcTc)
liftMonadicRecordUpdField given argty tcs (L l1 (HsRecField x (L l2 ambOcc) e pun)) = do
  ambOcc' <- liftAmbiguousFieldOcc tcs argty ambOcc
  e' <- liftMonadicExpr given argty tcs e
  return (L l1 (HsRecField x (L l2 ambOcc') e' pun))

liftMonadicRecordProjField :: [Ct] -> Type -> TyConMap -> LHsRecUpdProj GhcTc
                           -> TcM (LHsRecUpdProj GhcTc)
liftMonadicRecordProjField given argty tcs (L l1 (HsRecField x lbls e pun)) = do
    e' <- liftMonadicExpr given argty tcs e
    return (L l1 (HsRecField x lbls e' pun))

liftMonadicRecField :: [Ct] -> Type -> TyConMap
                    -> LHsRecField GhcTc (LHsExpr GhcTc)
                    -> TcM (LHsRecField GhcTc (LHsExpr GhcTc))
liftMonadicRecField given argty tcs (L l1 (HsRecField x (L l2 occ) e pun)) = do
  occ' <- liftFieldOcc tcs argty occ
  e' <- liftMonadicExpr given argty tcs e
  return (L l1 (HsRecField x (L l2 occ') e' pun))

-- for some weird reason, the "v" is not a selector function.
-- (It should be according to the doumentation)
-- By looking it up in the type environment again, we fix this.
liftFieldOcc :: TyConMap -> Type -> FieldOcc GhcTc -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs argty (FieldOcc v _) = do
  tenv <- tcg_type_env <$> getGblEnv
  case lookupTypeEnv tenv (varName v) of
    Just (AnId realV)
      | RecSelId parent _ <- idDetails realV
      -> do
        mty <- flip mkTyConApp [argty] <$> getMonadTycon
        stc <- getShareClassTycon
        ftc <- getFunTycon
        us <- getUniqueSupplyM
        v' <- liftIO (getLiftedRecSel stc ftc mty us tcs parent v)
        return (FieldOcc v' (noLocA (nameRdrName (varName v'))))
    _ -> panicBndr "Expected RecSel in FieldOcc of Record operation" v

liftAmbiguousFieldOcc :: TyConMap -> Type -> AmbiguousFieldOcc GhcTc
                      -> TcM (AmbiguousFieldOcc GhcTc)
liftAmbiguousFieldOcc tcs argty (Unambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs argty (FieldOcc v n)
  return (Unambiguous v' n')
liftAmbiguousFieldOcc tcs argty (Ambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs argty (FieldOcc v n)
  return (Ambiguous v' n')

liftTick :: TyConMap -> Type -> CoreTickish -> TcM CoreTickish
liftTick tcs argty (Breakpoint x i ids) = Breakpoint x i <$> mapM transId ids
  where
    transId v = setVarType v <$> liftTypeTcM tcs argty (varType v)
liftTick _ _ t = return t

shareVars :: TyConMap -> Type -> [(Var, LocatedN Var)] -> [Ct] -> LHsExpr GhcTc -> Type
          -> TcM (LHsExpr GhcTc)
shareVars tcs argty vs evs e' ety = do
  foldM (shareVar ety) e' $ reverse $ map (second unLoc)
                                    $ sortBy ((. snd) . cmpLocated . snd) vs
  where
    -- share v1 >>= \v2 -> e
    -- differs from the normal lifting, because we optimize for call-by-need
    shareVar ty e (v1,v2)
      | countVarOcc v2 e <= 1 = return (substitute v1 v2 e)
      | Many <- varMult v2     = do
        let v1e = noLocA (HsVar noExtField (noLocA v1))
        let v1ty = varType v1
        s <- noLocA . HsPar EpAnnNotUsed
          <$> mkAppWith (mkNewShareTh tcs argty) evs v1ty [v1e]
        mtycon <- getMonadTycon
        let sty = mkTyConApp mtycon [v1ty]
        let v2ty = Scaled (varMult v2) (varType v2)
        let l = noLocA (HsPar EpAnnNotUsed (mkLam (noLocA v2) v2ty e ty))
        mkBind s argty sty l ty
      -- Interestingly, we know that v1 and v2 do not ocurr more than once in e,
      -- as long as their multiplicity is not Many. Even if the multiplicity
      -- is polymorphic we know this, as the function could not have
      -- such a multiplicity if the function could not be linear in v1/v2.
      | otherwise = return (substitute v1 v2 e)

shareTopLevel :: Maybe Var -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
shareTopLevel Nothing  e = return e
shareTopLevel (Just v) e = do
  let u = varUnique v
  let i = getKey u
  mdl <- tcg_mod <$> getGblEnv
  let s = nameStableString (mkExternalName u mdl (occName v) noSrcSpan)
  mkApp (mkNewShareTop (i, s)) (varType v) [e]

substitute :: Data a => Var -> Var -> a -> a
substitute new old = everywhere (mkT substVar)
 where
    u = varName old
    substVar v = if varName v == u then new else v

{- HLINT ignore "Reduce duplication" -}
