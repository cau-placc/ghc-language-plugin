{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}
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

import Plugin.Trans.Constr
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
import Plugin.Trans.Enum

-- | Transform the given binding with a monadic lifting to incorporate
-- our nondeterminism as an effect.
-- This function also transforms any nested bindings recursively and
-- thus needs to know whether it is a local binding or not.
-- First  Bool: This is a local binding, swap the Unique for sharing purposes
-- Second Bool: This is a nested AbsBinds, do not insert into type env
liftMonadicBinding :: Bool -> Bool -> [Ct] -> TyConMap -> [ClsInst]
                   -> HsBindLR GhcTc GhcTc
                   -> TcM ([HsBindLR GhcTc GhcTc], [(Var,Var)])
liftMonadicBinding _ _ given tcs _ (FunBind wrap (L b name) eqs ticks) =
  setSrcSpan b $ addLandmarkErrCtxt ("In the definition of" <+> ppr name) $ do
  -- create the dictionary variables
  let (tvs, c) = collectTyDictArgs wrap
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
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
  ty <- liftTypeTcM tcs (varType name)
  let fullwrap = createWrapperLike ty tvs allEvs

  eqs' <- if isDerivedEnum eqs
    then liftDerivedEnumEquation tcs eqs
    else liftMonadicEquation given' tcs eqs
  ticks' <- mapM (liftTick tcs) ticks
  let name' = setVarType name ty
  return ([FunBind fullwrap (L b name') eqs' ticks'], [])
  where
    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)
liftMonadicBinding lcl _ given tcs _ (AbsBinds a b c d e f g)
  -- we do not want to lift dicts or record selectors or other system stuff here
  | all (noSystemNameOrRec . abe_poly) d = do

  -- create the dictionary variables
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
  uss <- replicateM (length b) getUniqueSupplyM
  let mkShareTy ty = mkTyConApp stc [mty, ty]
  let evsty = catMaybes $
              zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss b
  evs <- mapM freshDictId evsty
  lclEnv <- getLclEnv
  let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv

  allEvs <- (++evs) <$> liftIO (mapM replaceEv c)
  let cts = mkGivens ctloc allEvs
  let given' = given ++ cts


  (d', vs) <- unzip <$> mapM liftEx d
  let vs' = catMaybes vs

  -- lift inner bindings
  let bs = map unLoc (bagToList f)
  f' <- listToBag . map noLoc . concat
          <$> mapM (fmap fst . liftMonadicBinding False True given' tcs [])
              (foldr (\(n, o) -> substitute n o) bs vs')

  -- lift any original evidence that is exported. This is only relevant
  -- for standalone AbsBinds that bind any class parent dictionary
  -- Also keep any original evidence as-is, if this is a
  -- derived binding for enum
  e' <- if any isDerivedEnumBind bs
    then return e
    else mapM (liftEvidence given' tcs)
              (filter isExportedEv (concatMap flattenEv e))
  return ([AbsBinds a b allEvs d' e' f' g], vs')
  where
    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)

    -- Basically do the same as in liftTopTypes, but this time for
    -- both the poly and mono type and for local bindings as well
    liftEx :: ABExport GhcTc -> TcM (ABExport GhcTc, Maybe (Var,Var))
    liftEx (ABE x v1 v2 w p) = do
      -- change unique only for local decls, as only those are shared
      u <- if lcl then getUniqueM else return (varUnique v1)

      -- lift types
      mtycon <- getMonadTycon
      stycon <- getShareClassTycon
      us2 <- getUniqueSupplyM

      -- We only want to introduce Shareable constraints for the type
      -- variables bound in this AbsBind, so we manually split off
      -- all type and evidence abstractions bound here.
      -- Then we can do the lifting and stuff.
      -- All of this is only done, when a lifting is even required.
      let v1ty = varType v1
      ty1 <- case splitTyConApp_maybe (snd (splitPiTysInvisible v1ty)) of
        Just (tc, _) | tc == mtycon
          -> liftIO (replaceTyconTy tcs v1ty)
        _ -> do
          let (bs1, t1) = splitPiTysInvisibleN (length b + length c) v1ty
              named = filter isNamedBinder bs1
          uss <- replicateM (length named) getUniqueSupplyM
          let bs = map (\(Named b') -> b') named
              mkShareType t' = mkTyConApp stycon [mkTyConTy mtycon, t']
              cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
          bs1' <- liftIO (mapM (replacePiTy tcs) bs1)
          mkPiTys bs1' . flip (foldr mkInvisFunTyMany) cons
            <$> liftTypeTcM tcs t1

      -- The wrapper w deals with matching the impedence beteween the expected
      -- type of the exported function and the real type that is dictated by
      -- the type and evidence variables.
      -- See note [ABExport wrapper] in GHC.Hs.Binds.
      -- In addition to matching the type applications of the function,
      -- We also have to match the Shareable dictionaries
      -- that have been inserted.
      let (vs, rest) = collectHsWrapBinders w
          vswrap = foldr ((<.>) . WpTyLam) WpHole vs
          bs = map (flip Bndr Inferred) vs
          mkShareType t' = mkTyConApp stycon [mkTyConTy mtycon, t']
      uss <- replicateM (length vs) getUniqueSupplyM
      let cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
      convs <- mapM freshDictId cons
      let conwrap = foldr (flip (<.>) . WpEvLam) vswrap (reverse convs)
      -- For unused types, we can just apply GHC.Types.Any to them.
      -- For unused evidence, we cannot do this.
      -- Instead we create dummy evidence terms that have the right type
      -- by using unsafeCoerce.
      -- We know that the evidence is unused,
      -- because its type is Shareable Nondet Any.
      dfl <- getDynFlags
      let unsafeCoShare = Cast (mkIntExpr (targetPlatform dfl) 0)
            (mkUnivCo (PluginProv "unsafe") Representational
              intTy (mkShareType (anyTypeOfKind liftedTypeKind)))
      let ovs = repeat unsafeCoShare
      let evs = reverse $ zipWith ((,) . mkTyVarTy) vs convs
      let conapp = mkEvWrapSimilar rest ovs evs

      -- lift the mono type and create the new variables.
      ty2 <- liftIO (liftTypeIfRequired stycon mtycon us2 tcs (varType v2))
      let v2' = setVarType v2 ty2
      let v1' = setVarType v1 ty1
      -- also (possibly) change unique for sharing
      let v1u = setVarUnique v1' u

      return (ABE x v1u v2' (conwrap <.> (conapp <.> rest)) p, Just (v1u, v1'))

    -- Do not lift any system stuff, except instance fun definitions ($c) and
    -- class default methods ($dm).
    noSystemNameOrRec v = case occNameString (occName v) of
      n | "$con2tag_" `isPrefixOf` n -> False
      '$':'c':_     -> True
      '$':'d':'m':_ -> True
      '$':_         -> False
      _             -> not (isRecordSelector v)

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
    let HsApp x2 (L l3 (XExpr (WrapExpr (HsWrap (WpCompose w1 w2) e2)))) e3 = e1'

    mtycon <- getMonadTycon
    stycon <- getShareClassTycon
    -- Look at the number of abstractions in wrap.
    -- Those abstractions correspond to the vars bound in the instance head.
    -- Only for those we want Shareable.
    -- But only if the type is not lifted already.
    let numBinders = length (fst (collectHsWrapBinders wrap))
    let ty = varType name
    (ty', bndrs) <- case splitTyConApp_maybe (snd (splitPiTysInvisible ty)) of
      Just (tc, _) | tc == mtycon
        -> (,[]) <$> liftIO (replaceTyconTy tcs ty)
      _ -> do
        let (bs1, ty1) = splitPiTysInvisibleN numBinders ty
            named = filter isNamedBinder bs1
        uss <- replicateM (length named) getUniqueSupplyM
        let bs = map (\(Named b') -> b') named
            mkShareType t' = mkTyConApp stycon [mkTyConTy mtycon, t']
            cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
        bs1' <- liftIO (mapM (replacePiTy tcs) bs1)
        (,cons) . mkPiTys bs1' . flip (foldr mkInvisFunTyMany) cons
          <$> liftTypeTcM tcs ty1

    let name' = setVarType name ty'
    wrap' <- createAbstractionWrapperWith wrap bndrs
    w1' <- liftErrorWrapper tcs w1
    w2' <- liftErrorWrapper tcs w2
    let e1'' = HsApp x2 (L l3 (mkHsWrap (WpCompose w1' w2') e2)) e3
    return ([VarBind x1 name' (noLoc (mkHsWrap wrap' e1''))], [])
liftMonadicBinding _ _ _ _ _ a = return ([a], [])

-- The variables introduced here are guaranteed to be unused.
-- We just need to match the expected type.
createAbstractionWrapperWith :: HsWrapper -> [Type] -> TcM HsWrapper
createAbstractionWrapperWith w [] = return w
createAbstractionWrapperWith w (ty : tys) = do
  v <- freshDictId ty
  createAbstractionWrapperWith (w <.> WpEvLam v) tys

liftEvidence :: [Ct] -> TyConMap -> EvBind -> TcM TcEvBinds
liftEvidence given tcs (EvBind v _ _) = do
  -- Re-create constraints with the lifted constraint type
  -- This is only used for class parent dictionaries,
  -- so this is never a coercion that needs to be solved
  ty <- liftTypeTcM tcs (varType v)
  loc <- getCtLocM (OccurrenceOf (varName v)) Nothing
  let dst = EvVarDest (setVarType v ty)
  let cts = [CNonCanonical (CtWanted ty dst WDeriv loc)]
  -- solve them
  EvBinds <$> simplifyTop (WC (listToBag (cts ++ given)) emptyBag emptyBag)

liftLocalBinds :: [Ct] -> TyConMap -> LHsLocalBinds GhcTc
               -> TcM (LHsLocalBinds GhcTc, [(Var,Var)])
liftLocalBinds given tcs (L l (HsValBinds x b)) = do
  (b', vs) <- liftValBinds given tcs b
  return (L l (HsValBinds x b'), vs)
liftLocalBinds _ _ b@(L l (HsIPBinds _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return (b, [])
liftLocalBinds _ _ b = return (b, [])

liftValBinds :: [Ct] -> TyConMap -> HsValBindsLR GhcTc GhcTc
             -> TcM (HsValBindsLR GhcTc GhcTc, [(Var,Var)])
liftValBinds _ _ bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
liftValBinds given tcs (XValBindsLR (NValBinds bs _)) = do
  (bs', vss) <- unzip <$> mapM liftNV bs
  return (XValBindsLR (NValBinds bs' []), concat vss)
  where
    liftNV :: (RecFlag, LHsBinds GhcTc)
           -> TcM ((RecFlag, LHsBinds GhcTc), [(Var,Var)])
    liftNV (rf, b) = do
      let bs1 = map unLoc (bagToList b)
      (bs2, vss) <- first (map noLoc . concat) . unzip <$>
        mapM (liftMonadicBinding True False given tcs []) bs1
      return ((rf, listToBag bs2), concat vss)

liftMonadicEquation :: [Ct] -> TyConMap
                    -> MatchGroup GhcTc (LHsExpr GhcTc)
                    -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftMonadicEquation given tcs (MG a (L b alts) c) = do
  alts' <- mapM (liftMonadicAlt given tcs) alts
  a' <- liftMGTc tcs a
  return (MG a' (L b alts') c)

liftMGTc :: TyConMap -> MatchGroupTc -> TcM MatchGroupTc
liftMGTc tcs (MatchGroupTc args res) = do
  res' <- liftTypeTcM tcs res
  args' <- mapM (\(Scaled m ty) -> Scaled m <$> liftTypeTcM tcs ty) args
  return (MatchGroupTc args' res')

liftMonadicAlt :: [Ct] -> TyConMap
               -> LMatch GhcTc (LHsExpr GhcTc)
               -> TcM (LMatch GhcTc (LHsExpr GhcTc))
liftMonadicAlt given tcs (L a (Match b c d rhs)) = do
  (d', s, n) <- unzip3 <$> mapM (liftPattern tcs) d
  rhs' <- liftMonadicRhs (concat s) (concat n) given tcs rhs
  return (L a (Match b c d' rhs'))

liftMonadicRhs :: [(Var, Var)] -> [(Var, Var)] -> [Ct] -> TyConMap
               -> GRHSs GhcTc (LHsExpr GhcTc)
               -> TcM (GRHSs GhcTc (LHsExpr GhcTc))
liftMonadicRhs s n given tcs (GRHSs a grhs b) = do
  grhs' <- mapM (liftMonadicGRhs s n given tcs) grhs
  return (GRHSs a grhs' b)

liftMonadicGRhs :: [(Var, Var)] -> [(Var, Var)] -> [Ct] -> TyConMap
                -> LGRHS GhcTc (LHsExpr GhcTc)
                -> TcM (LGRHS GhcTc (LHsExpr GhcTc))
liftMonadicGRhs s n given tcs (L a (GRHS b c body)) = do
  body' <- liftMonadicExpr given tcs body
  body'' <- shareVars tcs s given body'
  L a . GRHS b c <$> foldM liftNewTyVar body'' n

liftMonadicExpr :: [Ct] -> TyConMap -> LHsExpr GhcTc
                -> TcM (LHsExpr GhcTc)
liftMonadicExpr given tcs (L _ (HsVar _ (L _ v))) =
  liftVarWithWrapper given tcs WpHole v
liftMonadicExpr given tcs (L _ (XExpr (WrapExpr (HsWrap w (HsVar _ (L _ v)))))) =
  liftVarWithWrapper given tcs w v
liftMonadicExpr _    tcs e@(L _ HsLit{}) = do
  ty <- getTypeOrPanic e
  lifted <- mkApp mkNewReturnTh ty [e]
  ty' <- liftIO (replaceTyconTy tcs ty)
  res <- mkApp (mkNewLiftETh ty) ty' [lifted]
  return $ noLoc $ HsPar noExtField res
liftMonadicExpr given tcs (L l (HsOverLit _ lit)) =
  case ol_witness lit of
    -- if this is geniunely a Double or Float, just wrap it with return
    e@(HsApp _ (L _ (HsConLikeOut _ (RealDataCon dc))) _)
      | dc == doubleDataCon || dc == floatDataCon -> do
        ty <- getTypeOrPanic (noLoc e)
        mkApp mkNewReturnTh ty [noLoc e]
    -- otherwise, just lift the witness
    _ -> liftMonadicExpr given tcs (L l (ol_witness lit))
liftMonadicExpr given tcs (L l (HsLam _ mg)) =
  liftLambda given tcs l Nothing mg
liftMonadicExpr given tcs (L l (HsLamCase _ mg)) =
  liftLambda given tcs l Nothing mg
liftMonadicExpr _ tcs (L _ (HsConLikeOut _ (RealDataCon c))) = do
  c' <- liftIO (getLiftedCon c tcs)
  let tys = dataConOrigArgTys c'
  e <- fst <$> mkConLam Nothing c' tys []
  return $ noLoc $ HsPar noExtField e
liftMonadicExpr _ tcs (L _ (XExpr (WrapExpr (HsWrap w (HsConLikeOut _ (RealDataCon c)))))) = do
  c' <- liftIO (getLiftedCon c tcs)
  w' <- liftWrapperTcM (not $ isNewTyCon (dataConTyCon c')) tcs w
  let (apps, absts) = collectTyApps w'
      realApps = drop (length absts) apps
  let tys = conLikeInstOrigArgTys (RealDataCon c') realApps
  e <- fst <$> mkConLam (Just w') c' tys []
  return $ noLoc $ HsPar noExtField e
liftMonadicExpr given tcs (L _ (OpApp _ e1 op e2)) = do
  -- e1 `op` e2
  -- -> op >>= \f -> f e1 >>= \f -> f e2
  e1' <- liftMonadicExpr given tcs e1
  op' <- liftMonadicExpr given tcs op
  e2' <- liftMonadicExpr given tcs e2
  opty1 <- getTypeOrPanic op'
  let (_, _, opty2) = splitFunTy $ bindingType opty1
  let (_, _, opty3) = splitFunTy $ bindingType opty2
  e1'' <- mkBindLam (Scaled Many opty1) e1'
  op'' <- mkBind op' opty1 e1'' opty2
  e2'' <- mkBindLam (Scaled Many opty2) e2'
  res <- mkBind op'' opty2 e2'' opty3
  return $ noLoc $ HsPar noExtField res
-- if this is an application of a function to a lambda, where
-- the function argument has a forall'd polymorphic type,
-- we need more than just lifting of HsApp + lifting of HsLam.
liftMonadicExpr given tcs (L l1 (HsApp _ fn (L l2 (HsLam _ mg)))) = do
  fn' <- liftMonadicExpr given tcs fn
  funty <- getTypeOrPanic fn'
  mtc <- getMonadTycon
  stc <- getShareClassTycon
  (unlifted, _) <- liftIO $ removeNondet tcs mtc stc funty
  let (bs, rest) = splitPiTysInvisible unlifted
  ex' <- if notNull bs
    then do
      -- TODO missing any previous constraints.

      -- Get the type variable bound by each binder.
      let anyVs = filter isTyVar $ map (\(Named (Bndr b' _)) -> b') $
                  filter isNamedBinder bs
      -- Create new type variables with the same kinds
      instVs <- mapM (freshTVar . tyVarKind) anyVs
      -- Create the type lambdas required by the forall'd variables.
      let abstsWrap' = foldr ((<.>) . WpTyLam) WpHole instVs

      -- Create a Shareable dict for each of the abstracted variables.
      let mkShareTy ty = mkTyConApp stc [mkTyConTy mtc, ty]
      uss <- replicateM (length instVs) getUniqueSupplyM
      let evsty = catMaybes $
                  zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss
                    instVs
      evs <- mapM freshDictId evsty
      lclEnv <- getLclEnv
      let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv
      let given' = mkGivens ctloc evs ++ given

      -- finally lift the lambda and pass the type we try to create
      liftLambda given' tcs l2 (Just rest) mg
    else liftLambda given tcs l2 Nothing mg

  let (_, _, exty) = splitFunTy $ bindingType funty
  ex'' <- mkBindLam (Scaled Many funty) ex'
  res <- mkBind fn' funty ex'' exty
  return $ noLoc $ HsPar noExtField res
liftMonadicExpr given tcs (L _ (HsApp _ fn ex)) = do
  -- e1 e2
  -- -> e1 >>= \f -> f e2
  fn' <- liftMonadicExpr given tcs fn
  funty <- getTypeOrPanic fn'
  ex' <- liftMonadicExpr given tcs ex
  let (_, _, exty) = splitFunTy $ bindingType funty
  ex'' <- mkBindLam (Scaled Many funty) ex'
  res <- mkBind fn' funty ex'' exty
  return $ noLoc $ HsPar noExtField res
liftMonadicExpr given tcs (L _ (HsAppType _ e _)) =
  liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (NegApp _ e (SyntaxExprTc n ws w))) =
  liftMonadicExpr given tcs (L l (mkHsWrap w
    (HsApp noExtField (noLoc n) (fmap (mkHsWrap (head ws)) e))))
liftMonadicExpr _ _ (L _ (NegApp _ _ NoSyntaxExprTc)) = undefined
liftMonadicExpr given tcs (L l (HsPar x e)) =
  L l . HsPar x <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (SectionL _ e1 e2)) =
  liftMonadicExpr given tcs (L l (HsApp noExtField e2 e1))
liftMonadicExpr given tcs (L _ (SectionR _ e1 e2)) = do
  ty <- getTypeOrPanic e1
  let (m1, arg1, ty') = splitFunTy ty
  let (_ , _   , res) = splitFunTy ty'
  v <- noLoc <$> freshVar (Scaled m1 arg1)
  liftMonadicExpr given tcs
    (mkLam v (Scaled Many ty)
    (mkHsApp (mkHsApp e1 (noLoc (HsVar noExtField v))) e2) res)
liftMonadicExpr given tcs (L _ (ExplicitTuple _ args b)) =
  liftExplicitTuple given tcs args b
liftMonadicExpr _    _   e@(L l ExplicitSum {}) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsCase _ scr br)) = do
  br'@(MG (MatchGroupTc _ ty2) _ _) <- liftMonadicEquation given tcs br
  scr' <- liftMonadicExpr given tcs scr
  ty1 <- getTypeOrPanic scr'
  mkBind scr' ty1 (noLoc $ HsPar noExtField $ L l $ HsLamCase noExtField br') ty2
liftMonadicExpr given tcs (L l (HsIf _ e1 e2 e3)) = do
  -- if e1 then e2 else e3
  -- -> e1 >>= \case { True -> e1; _ -> e2 }
  e1' <- liftMonadicExpr given tcs e1
  e2' <- liftMonadicExpr given tcs e2
  e3' <- liftMonadicExpr given tcs e3
  ty1' <- getTypeOrPanic e1'
  ty2' <- getTypeOrPanic e2'
  let ty1 = bindingType ty1'
  v <- noLoc <$> freshVar (Scaled Many ty1)
  let ife = HsIf noExtField (noLoc (HsVar noExtField v)) e2' e3'
  let alt = mkSimpleAlt LambdaExpr (noLoc ife) [noLoc (VarPat noExtField v)]
  let mgtc = MatchGroupTc [Scaled Many ty1] ty2'
  let mg = MG mgtc (noLoc [noLoc alt]) Generated
  mkBind e1' ty1' (noLoc $ HsPar noExtField $ L l $ HsLam noExtField mg) ty2'
liftMonadicExpr _ _ e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
liftMonadicExpr given tcs (L l (HsLet x bs e)) = do
  -- Lift local binds first, so that they end up in the type environment.
  (bs', vs) <- liftLocalBinds given tcs bs
  e' <- liftMonadicExpr given tcs e
  e'' <- shareVars tcs vs given e'
  return (L l (HsLet x bs' e''))
liftMonadicExpr given tcs (L l1 (HsDo x ctxt (L l2 stmts))) = do
  x' <- liftTypeTcM tcs x
  -- Because ListComp are not overloadable,
  -- we have to change them to MonadComp.
  let ctxtSwitch | ListComp <- ctxt = True
                 | otherwise        = False
  let ctxt' | ctxtSwitch = MonadComp
            | otherwise  = ctxt
  stmts' <- liftMonadicStmts ctxt' ctxtSwitch x' given tcs stmts
  return (L l1 (HsDo x' ctxt' (L l2 stmts')))
liftMonadicExpr given tcs (L _ (ExplicitList ty Nothing es)) = do
  -- [e1, ..., en]
  -- -> return (Cons e1 (return (Cons ... (return (Cons en (return Nil))))))
  em <- mkEmptyList ty tcs
  liftedTy <- getTypeOrPanic em
  nil <- mkApp mkNewReturnTh liftedTy [em]
  if null es
    then return nil
    else do
      es' <- mapM (liftMonadicExpr given tcs) es
      cons <- mkConsList ty tcs
      let mkCons e1 e2 = let e' = mkHsApp (mkHsApp cons e1) e2
                         in mkApp mkNewReturnTh liftedTy [e']
      foldrM mkCons nil es'
liftMonadicExpr _ _ e@(L l (ExplicitList _ (Just _) _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs
  (L l1 (RecordCon (RecordConTc (RealDataCon c) ce) (L l2 _) fs)) = do
    c' <- liftIO (getLiftedCon c tcs)
    let cn' = dataConWorkId c'
    ce' <- liftConExpr tcs c' ce
    fs' <- liftMonadicRecFields given tcs fs
    let e = L l1 (RecordCon (RecordConTc (RealDataCon c') ce') (L l2 cn') fs')
    if isNewTyCon (dataConTyCon c')
      then return e
      else getTypeOrPanic e >>= flip (mkApp mkNewReturnTh) [e]
liftMonadicExpr _ _ e@(L l (RecordCon (RecordConTc (PatSynCon _) _) _ _)) = do
    flags <- getDynFlags
    reportError (mkErrMsg flags l neverQualify
      "Pattern synonyms are not supported by the plugin")
    failIfErrsM
    return e
liftMonadicExpr given tcs (L l (RecordUpd rtc e fs)) = do
  rtc'@(RecordUpdTc (c:_) inty outty _)  <- liftMonadicRecordUpd tcs rtc
  e' <- liftMonadicExpr given tcs e
  fs' <- mapM (liftMonadicRecordUpdField given tcs) fs
  let vty = conLikeResTy c inty
  v <- noLoc <$> freshVar (Scaled Many vty)
  let upd = L l (RecordUpd rtc' (noLoc (HsVar noExtField v)) fs')
  let updTy = conLikeResTy c outty
  let updLam = mkLam v (Scaled Many vty) upd updTy
  mkApp (mkNewFmapTh vty) updTy [updLam, e']
liftMonadicExpr given tcs (L _ (ExprWithTySig _ e _)) =
  liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L _ (ArithSeq x Nothing i)) =
  liftMonadicExpr given tcs (foldl mkHsApp (noLoc x) (arithSeqArgs i))
liftMonadicExpr _ _ e@(L l (ArithSeq _ (Just _) _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsPragE x (HsPragSCC a b c) e)) =
  L l . HsPragE x (HsPragSCC a b c) <$> liftMonadicExpr given tcs e
liftMonadicExpr _ _ e@(L l (HsBracket _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L l (HsSpliceE _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L l (HsTcBracketOut _ _ _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L l (HsProc _ _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Arrow notation is not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsStatic x e)) =
  L l . HsStatic x <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsTick a tick e)) = do
  (L l .) . HsTick a <$> liftTick tcs tick <*> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsBinTick a b c e)) =
  L l . HsBinTick a b c <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (XExpr (WrapExpr (HsWrap w e)))) = do
  e' <- unLoc <$> liftMonadicExpr given tcs (L l e)
  w' <- liftWrapperTcM True tcs w
  return (L l (mkHsWrap w' e'))
liftMonadicExpr _ _ (L _ (HsUnboundVar _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsRecFld _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsOverLabel _ _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsIPVar _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsRnBracketOut _ _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsConLikeOut _ _)) = undefined
liftMonadicExpr _ _ (L _ (XExpr (ExpansionExpr _))) = undefined

liftMonadicStmts :: HsStmtContext GhcRn -> Bool -> Type -> [Ct] -> TyConMap
                 -> [ExprLStmt GhcTc] -> TcM [ExprLStmt GhcTc]
liftMonadicStmts _ _ _ _ _ [] = return []
liftMonadicStmts ctxt ctxtSwitch ty given tcs (s:ss) = do
  (s', vs) <- liftMonadicStmt s
  ss' <- liftMonadicStmts ctxt ctxtSwitch ty given tcs ss
  if null vs
    then return (s':ss')
    else do
      e <- shareVars tcs vs given (noLoc (HsDo ty ctxt (noLoc ss')))
      return [s', noLoc (LastStmt noExtField e Nothing NoSyntaxExprTc)]
  where
    liftMonadicStmt :: ExprLStmt GhcTc -> TcM (ExprLStmt GhcTc, [(Var, Var)])
    liftMonadicStmt (L l (LastStmt x e a r)) = do
      e' <- liftMonadicExpr given tcs e
      r' <- if synExprExists r
              then trans1 r
              else return r
      return (L l (LastStmt x e' a r'), [])
    liftMonadicStmt (L l (BindStmt (XBindStmtTc b m x f) p e)) = do
      -- p is definitely just a varPat and f is NoSyntaxExprTc or Nothing
      (p', vs, _) <- liftPattern tcs p
      e' <- liftMonadicExpr given tcs e
      x' <- liftTypeTcM tcs x
      b' <- transBind b
      return (L l (BindStmt (XBindStmtTc b' m x' f) p' e'), vs)
    liftMonadicStmt (L l (ApplicativeStmt _ _ _)) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Applicative do-notation is not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l (BodyStmt x e se g)) = do
      x' <- liftTypeTcM tcs x
      e' <- liftMonadicExpr given tcs e
      se' <- trans2 se
      g' <- if synExprExists g
              then trans1 g
              else return g
      return (L l (BodyStmt x' e' se' g'), [])
    liftMonadicStmt (L l (LetStmt x bs)) = do
      (bs', vs) <- liftLocalBinds given tcs bs
      return (L l (LetStmt x bs'), vs)
    liftMonadicStmt (L l (ParStmt _ _ _ _)) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l (TransStmt _ _ _ _ _ _ _ _ _)) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l (RecStmt _ _ _ _ _ _ _)) =  do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Recursive do-notation is not supported by the plugin")
      failIfErrsM
      return (s, [])

    synExprExists se | HsLit _ _ <- syn_expr se = False
                     | otherwise                = True

    trans1 (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLoc (mkHsWrap w e))
      e1ty <- getTypeOrPanic e1
      let (_, ty1, ty2) = splitFunTy (bindingType e1ty)
      e2 <- mkApp (mkNewApply1 (bindingType ty1)) (bindingType ty2) [e1]
      ws' <- mapM (liftWrapperTcM True tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    trans1 NoSyntaxExprTc = return NoSyntaxExprTc

    transBind (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLoc (mkHsWrap w e))
      e1ty <- getTypeOrPanic e1
      let (_, ty1, restty) = splitFunTy (bindingType e1ty)
      let (_, ty2, ty3) = splitFunTy (bindingType restty)
      e2 <- mkApp (mkNewApply2Unlifted (bindingType ty1) (bindingType ty2))
                  (bindingType ty3) [e1]
      ws' <- mapM (liftWrapperTcM True tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    transBind NoSyntaxExprTc = return NoSyntaxExprTc

    trans2 (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLoc (mkHsWrap w e))
      e1ty <- getTypeOrPanic e1
      let (_, ty1, restty) = splitFunTy (bindingType e1ty)
      let (_, ty2, ty3) = splitFunTy (bindingType restty)
      e2 <- mkApp (mkNewApply2 (bindingType ty1) (bindingType ty2))
                  (bindingType ty3) [e1]
      ws' <- mapM (liftWrapperTcM True tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    trans2 NoSyntaxExprTc = return NoSyntaxExprTc

liftLambda :: [Ct] -> TyConMap -> SrcSpan
           -> Maybe Type -> MatchGroup GhcTc (LHsExpr GhcTc) -> TcM (LHsExpr GhcTc)
liftLambda given tcs l mb mg = do
  mg'@(MG (MatchGroupTc [Scaled m arg] res) _ _)
    <- liftMonadicEquation given tcs mg
  let e = L l (HsLam noExtField mg')
  let ty = mkVisFunTy m arg res
  mkApp mkNewReturnTh ty [noLoc (HsPar noExtField e)]

-- We need to pay special attention to a lot of different kinds of variables.
-- Most of those kinds can be treated sinilarly (see below), but for
-- record selectors, we need a different approach.
liftVarWithWrapper :: [Ct] -> TyConMap -> HsWrapper -> Var
                   -> TcM (LHsExpr GhcTc)
liftVarWithWrapper given' tcs w v
  | isRecordSelector v = do
    -- lift type
    mty <- mkTyConTy <$> getMonadTycon
    stc <- getShareClassTycon
    w' <- liftWrapperTcM True tcs w
    us <- getUniqueSupplyM

    let (apps, abstrs) = collectTyApps w'
    let realApps = drop (length abstrs) apps
    let (_, arg, res) = splitFunTy (instantiateWith realApps (varType v))

    let p = sel_tycon (idDetails v)
    v' <- liftIO (getLiftedRecSel stc mty us tcs p v)

    let vExpr = noLoc (mkHsWrap w' (HsVar noExtField (noLoc v')))
    e <- case p of
      RecSelData tc
        -- translate any newtype  record selector "sel" to "return (fmap sel)"
        | isNewTyCon tc -> mkApp (mkNewFmapTh arg) res [vExpr]
        -- translate any datatype record selector "sel" to "return (>>= sel)"
      _                 -> noLoc . flip (SectionR noExtField) vExpr <$>
                             mkApp (mkNewBindTh arg) (bindingType res) []
    ety <- getTypeOrPanic e
    mkApp mkNewReturnTh ety [noLoc (HsPar noExtField e)]
  | otherwise          = do
  -- lift type
  w' <- liftWrapperTcM True tcs w
  stc <- getShareClassTycon
  mtc <- getMonadTycon
  us <- getUniqueSupplyM
  ty' <- liftIO (liftTypeIfRequired stc mtc us tcs (varType v))

  let (aps, absts) = collectTyApps w'

  -- In the case of higher-rank polymorphic arguments,
  -- the constraint solver might force GHC to instantiate the forall'd variables
  -- of the higher-rank argument with 'Any' instead of creating a proper type
  -- abstraction.
  -- E.g. if we use
  -- build :: forall a. (forall b . (a -> b -> b) -> b -> b) -> [a]
  -- and apply it to a function test, we end up with
  -- build (testX @Any)
  -- instead of the proper
  -- build (/\b -> testX @b)

  -- Collect any applicatons of 'Any'.
  let (anyApps,  otherApps) = flip partition aps $ \t ->
                                eqType t (anyTypeOfKind (typeKind t))
  -- Get as many pi type binder (e.g. foralls) as there are 'Any' applicatons.
  let anyPis = fst $ splitPiTysInvisibleN (length anyApps) (varType v)
  -- Get the type variable bound by each binder.
  let anyVs = filter isTyVar              $ map (\(Named (Bndr b' _)) -> b') $
              filter isNamedBinder anyPis
  -- Create new type variables with the same kinds
  instVs <- mapM (freshTVar . tyVarKind) anyVs
  -- Replace the applications of 'Any' with the new variables
  let apps = map mkTyVarTy instVs ++ otherApps
  -- Re-Create the original type lambdas and add the ones required by
  -- the 'Any' applications.
  let allAbsts = instVs ++ absts
  let abstsWrap' = foldr ((<.>) . WpTyLam) WpHole allAbsts

  -- Create a Shareable dict for each of the abstracted variables.
  let mkShareTy ty = mkTyConApp stc [mkTyConTy mtc, ty]
  uss <- replicateM (length allAbsts) getUniqueSupplyM
  let evsty = catMaybes $
              zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss
                allAbsts
  evs <- mapM freshDictId evsty
  lclEnv <- getLclEnv
  let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv
  let given = mkGivens ctloc evs ++ given'

  -- Add dicts to the abstraction wrapper
  let abstsWrap = abstsWrap' <.> foldr ((<.>) . WpEvLam) WpHole evs

  -- 1. If it is a typeclass operation, we re-create it from scratch to get
  --    the unfolding information right.
  -- 2. If it is a default method,
  --    we have to set the correct type and
  --    switch to the correct default method.
  --    For an imported default method,
  --    we have to make some adjustments to the lifting.
  -- 3. If it is a LclId, just use the lifted type.
  -- 4. If it is one of a specific set of methods from the Prelude
  --    (due to deriving), we have to switch to the correct method.
  --    This falls back to jus returning the current identifier,
  --    If no replacement function is found.
  let mv' | ClassOpId cls <- idDetails v = do
            cls' <- liftIO (getLiftedClass cls tcs)
            -- lookup the corresponding new name for the selector
            let sels = map idName (classAllSelIds cls)
                sels' = map idName (classAllSelIds cls')
                Just (_, idx) = find ((== varName v) . fst) (zip sels [0..])
                -- if the class happens to be OrdND, we have to add 1 to idx
                name = sels' !! idx
            return (mkDictSelId name cls')
          | '$':'d':'m':_ <- occNameString (occName v) = do
            -- Split the type to get the class that this is the default method
            -- for, and look up the new version of that class.
            let tc = tyConAppTyCon (funArgTy (snd (splitForAllTys (varType v))))
            tc' <- liftIO (lookupTyConMap GetNew tcs tc)
            if tc == tc' -- if they are equal, this is NOT a built-in class.
              then if isLocalId v
                then
                  let Just cls = tyConClass_maybe tc
                  in setVarType v <$> liftDefaultType tcs cls (varType v)
                else -- If imported, v is almost typed correctly.
                  setVarType v <$> liftIO (replaceTyconTy tcs (varType v))
              -- Otherwise, look up the replacement of the default method.
              else
                lookupDefaultReplacement tc tc' (varName v)
          | isLocalId v =
            return (setVarType v ty')
          | otherwise = lookupWiredInFunc v
  v' <- mv'

  let monotype = instantiateWith apps (varType v')
      getPred (Anon _ (Scaled _ t))
        | all (\cv -> countVarOcc cv t == 0) absts
                = Just t
      getPred _ = Nothing
      preds = mapMaybe getPred (fst (splitPiTysInvisible monotype))

  if null preds
    then do
      let newWrap = abstsWrap <.> createWrapperFor (varType v') apps []
      return (noLoc (mkHsWrap newWrap (HsVar noExtField (noLoc v'))))
    else do
      -- construct wanted constraints
      wanted <- newWanteds (OccurrenceOf (varName v')) preds
      let evvars = map (\a -> let EvVarDest d = ctev_dest a in d) wanted
      let cts = map CNonCanonical wanted
      -- solve them
      evidence <- mkWpLet . EvBinds <$>
        simplifyTop (WC (listToBag (cts ++ given)) emptyBag emptyBag)

      -- create the new wrapper, with the new dicts and the type applications
      let wdict = createWrapperFor (varType v') apps evvars
      let wall = abstsWrap <.> (evidence <.> wdict)
      zonkTopLExpr (noLoc $ mkHsWrap wall $ HsVar noExtField $ noLoc v')

-- (,b,) = return $ \x1 -> return $ \x2 -> return (x1, b, x2)
liftExplicitTuple :: [Ct] -> TyConMap -> [LHsTupArg GhcTc]
                  -> Boxity -> TcM (LHsExpr GhcTc)
liftExplicitTuple given tcs args b = liftExplicitTuple' [] WpHole args
  where
    liftExplicitTuple' :: [LHsExpr GhcTc] -> HsWrapper -> [LHsTupArg GhcTc]
                       -> TcM (LHsExpr GhcTc)
    liftExplicitTuple' col w (L _ (Present _ e) : xs) = do
      e' <- liftMonadicExpr given tcs e
      ty <- getTypeOrPanic e'
      liftExplicitTuple' (e' : col) (WpTyApp (bindingType ty) <.> w) xs
    liftExplicitTuple' col w (L _ (Missing (Scaled m ty)) : xs) = do
      ty' <- liftTypeTcM tcs ty
      v <- noLoc <$> freshVar (Scaled m ty')
      let arg = noLoc (HsVar noExtField v)
      inner <- liftExplicitTuple' (arg:col) (WpTyApp (bindingType ty') <.> w) xs
      resty <- getTypeOrPanic inner
      let lam = mkLam v (Scaled m ty') inner resty
      mkApp mkNewReturnTh (mkVisFunTyMany ty' resty) [lam]
    liftExplicitTuple' col w [] = do
      let exprArgs = reverse col
      dc <- liftIO (getLiftedCon (tupleDataCon b (length exprArgs)) tcs)
      let ce = mkHsWrap w (HsConLikeOut noExtField (RealDataCon dc))
      let appCe = foldl mkHsApp (noLoc ce) exprArgs
      ty <- getTypeOrPanic appCe
      mkApp mkNewReturnTh ty [appCe]

-- This is for RecordConstructors only.
-- We are interested in lifting the (potential wrapper)
-- and we want to replace the HsConLike with the lifted constructor version.
-- HsConLike is the only sensible option for this PostTcExpr for Haskell2010.
liftConExpr :: TyConMap -> DataCon -> PostTcExpr -> TcM PostTcExpr
liftConExpr tcs dc (XExpr (WrapExpr (HsWrap w _)))
  | isNewTyCon (dataConTyCon dc) = liftNewConExpr (Just w) tcs dc
  | otherwise = do
    w' <- liftWrapperTcM True tcs w
    return (mkHsWrap w' (HsConLikeOut noExtField (RealDataCon dc)))
liftConExpr tcs dc _
  | isNewTyCon (dataConTyCon dc) = liftNewConExpr Nothing tcs dc
  | otherwise = return (HsConLikeOut noExtField (RealDataCon dc))

liftNewConExpr :: Maybe HsWrapper -> TyConMap -> DataCon -> TcM PostTcExpr
liftNewConExpr mw tcs dc = do
  -- lift wrapper
  mty <- mkTyConTy <$> getMonadTycon
  w' <- case mw of
    Just w  -> liftWrapperTcM False tcs w
    Nothing -> return WpHole

  -- get the argument type
  let (apps, absts) = collectTyApps w'
  let realApps = drop (length absts) apps
  let [Scaled m ty] = conLikeInstOrigArgTys (RealDataCon dc) realApps
  let ty' = mkAppTy mty ty

  -- create a fresh var with that type
  v <- freshVar (Scaled Many ty')

  -- create the constructor mapped with "fmap" over v
  let de = HsConLikeOut noExtField (RealDataCon dc)
  let ce = noLoc (mkHsWrap w' de)
  let arg = noLoc (HsVar noExtField (noLoc v))
  cetype <- funResultTy <$> getTypeOrPanic ce
  let argtype = bindingType (varType v)
  e <- mkApp (mkNewFmapTh argtype) cetype [ce, arg]

  -- return lambda abstraction
  return (unLoc (mkLam (noLoc v) (Scaled m ty') e (mkAppTy mty cetype)))

liftMonadicRecFields :: [Ct] -> TyConMap
                     -> HsRecordBinds GhcTc
                     -> TcM (HsRecordBinds GhcTc)
liftMonadicRecFields given tcs (HsRecFields flds dotdot) =
  flip HsRecFields dotdot <$> mapM (liftMonadicRecField given tcs) flds

liftMonadicRecordUpd :: TyConMap -> RecordUpdTc -> TcM RecordUpdTc
liftMonadicRecordUpd tcs (RecordUpdTc cs intys outtys wrap) = do
  RecordUpdTc <$> mapM conLike cs
              <*> mapM (liftInnerTyTcM tcs) intys
              <*> mapM (liftInnerTyTcM tcs) outtys
              <*> liftWrapperTcM True tcs wrap
  where
    conLike (RealDataCon c) = RealDataCon <$> liftIO (getLiftedCon c tcs)
    conLike p@(PatSynCon _) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags noSrcSpan neverQualify
        "Pattern synonyms are not supported by the plugin")
      failIfErrsM
      return p

liftMonadicRecordUpdField :: [Ct] -> TyConMap -> LHsRecUpdField GhcTc
                          -> TcM (LHsRecUpdField GhcTc)
liftMonadicRecordUpdField given tcs (L l1 (HsRecField (L l2 ambOcc) e pun)) = do
  ambOcc' <- liftAmbiguousFieldOcc tcs ambOcc
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField (L l2 ambOcc') e' pun))

liftMonadicRecField :: [Ct] -> TyConMap
                    -> LHsRecField GhcTc (LHsExpr GhcTc)
                    -> TcM (LHsRecField GhcTc (LHsExpr GhcTc))
liftMonadicRecField given tcs (L l1 (HsRecField (L l2 occ) e pun)) = do
  occ' <- liftFieldOcc tcs occ
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField (L l2 occ') e' pun))

-- for some weird reason, the "v" is not a selector function.
-- (It should be according to the doumentation)
-- By looking it up in the type environment again, we fix this.
liftFieldOcc :: TyConMap -> FieldOcc GhcTc -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs (FieldOcc v _) = do
  tenv <- tcg_type_env <$> getGblEnv
  let Just (AnId realV) = lookupTypeEnv tenv (varName v)
  case idDetails realV of
    RecSelId parent _ -> do
      mty <- mkTyConTy <$> getMonadTycon
      stc <- getShareClassTycon
      us <- getUniqueSupplyM
      v' <- liftIO (getLiftedRecSel stc mty us tcs parent v)
      return (FieldOcc v' (noLoc (nameRdrName (varName v'))))
    _ -> panicBndr "Expected RecSel in FieldOcc of Record operation" v

liftAmbiguousFieldOcc :: TyConMap -> AmbiguousFieldOcc GhcTc
                      -> TcM (AmbiguousFieldOcc GhcTc)
liftAmbiguousFieldOcc tcs (Unambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs (FieldOcc v n)
  return (Unambiguous v' n')
liftAmbiguousFieldOcc tcs (Ambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs (FieldOcc v n)
  return (Ambiguous v' n')

liftTick :: TyConMap -> Tickish Var -> TcM (Tickish Var)
liftTick tcs (Breakpoint i ids) = Breakpoint i <$> mapM transId ids
  where
    transId v = setVarType v <$> liftTypeTcM tcs (varType v)
liftTick _ t = return t

liftNewTyVar :: LHsExpr GhcTc -> (Var, Var) -> TcM (LHsExpr GhcTc)
liftNewTyVar e (old, new) = do
  le <- mkApp mkNewReturnTh (varType old) [noLoc (HsVar noExtField (noLoc old))]
  ty <- flip mkTyConApp [varType old] <$> getMonadTycon
  return (noLoc (mkSimpleLet NonRecursive le e new ty))

shareVars :: TyConMap -> [(Var, Var)] -> [Ct] -> LHsExpr GhcTc
          -> TcM (LHsExpr GhcTc)
shareVars tcs vs evs e' = do
  ty <- getTypeOrPanic e'
  foldM (shareVar ty) e' vs
  where
    -- share v1 >>= \v2 -> e
    shareVar ty e (v1,v2)
      | countVarOcc v2 e <= 1 = return (substitute v1 v2 e)
      | Many <- varMult v2     = do
        let v1e = noLoc (HsVar noExtField (noLoc v1))
        let v1ty = varType v1
        s <- noLoc . HsPar noExtField
          <$> mkAppWith (mkNewShareTh tcs) evs v1ty [v1e]
        mtycon <- getMonadTycon
        let sty = mkTyConApp mtycon [v1ty]
        let v2ty = Scaled (varMult v2) (varType v2)
        let l = noLoc (HsPar noExtField (mkLam (noLoc v2) v2ty e ty))
        ety <- getTypeOrPanic e
        mkBind s sty l ety
      -- Interestingly, we know that v1 and v2 do not ocurr more than once in e,
      -- as long as their multiplicity is not Many. Even if the multiplicity
      -- is polymorphic we know this, as the function could not have
      -- such a multiplicity if the function could not be linear in v1/v2.
      | otherwise = return (substitute v1 v2 e)

substitute :: Data a => Var -> Var -> a -> a
substitute new old = everywhere (mkT substVar)
 where
    u = varName old
    substVar v = if varName v == u then new else v

{- HLINT ignore "Reduce duplication" -}
