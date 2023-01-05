{-# LANGUAGE TupleSections #-}
{-|
Module      : Plugin.Trans.Derive
Description : Create internal derive declarations for data types
Copyright   : (c) Kai-Oliver Prott (2020 - 2023)
Maintainer  : kai.prott@hotmail.de

This module contains a function to create deriving declarations for
a given set of lifted and unlifted type constructors.
We create deriving declarations for Generic, Shareable and Normalform.
-}
module Plugin.Trans.Derive (mkDerivings) where

import Data.Maybe
import Language.Haskell.Syntax.Extension

import GHC.Hs.Extension
import GHC.Hs.Type
import GHC.Hs.Decls
import GHC.Hs.Utils
import GHC.Types.Name.Occurrence hiding (varName)
import GHC.Plugins hiding (substTy, extendTvSubst)
import GHC.Tc.Types
import GHC.Tc.Utils.TcType
import GHC.Core.TyCo.Rep
import GHC.Parser.Annotation

import Plugin.Trans.Type

-- | Create standalone deriving declarations for
-- Generic, Shareable and Normalform.
mkDerivings :: [(TyCon, TyCon)] -> TcM [LDerivDecl GhcRn]
mkDerivings tc = do
  gen <- mapM mkDerivingGen tc
  sha <- mapM mkDerivingShare tc
  nor <- mapM mkDerivingNF tc
  return (concat gen ++ catMaybes (sha ++ nor))

-- | Create standalone deriving declaration for Generic.
mkDerivingGen :: (TyCon, TyCon) -> TcM [LDerivDecl GhcRn]
mkDerivingGen (old, new) | isVanillaAlgTyCon new = do
  -- Create Generic class type.
  gname <- tyConName <$> getGenericClassTycon
  let gty = toTy gname
  let clsty = gty

  -- Get the lifted type constructor type.
  let newtyconty = toTy (tyConName new)
  -- Get all type variables of the lifted type constructor.
  let newvars = map (varName . fst) $ visTyConTyVarsRoles new

  -- Apply the class to the fully saturated lifted type constructor.
  let newbdy = mkHsAppTy clsty (foldr appVars newtyconty (reverse newvars))
  let newty = newbdy
  let newtysig = HsSig noExtField (HsOuterImplicit newvars) newty
  -- Add the type variables to the set of bound variables.
  let newinstty = mkEmptyWildCardBndrs $ noLocA newtysig
  -- Create the deriving declaration for the lifted type constructor.
  let newdecl = DerivDecl EpAnnNotUsed newinstty Nothing Nothing

  -- Do the same for the old type constructor.
  let oldtyconty = toTy (tyConName old)
  let oldvars = map (varName . fst) $ visTyConTyVarsRoles old
  let oldbdy = mkHsAppTy clsty (foldr appVars oldtyconty oldvars)
  let oldty = oldbdy
  let oldtysig = HsSig noExtField (HsOuterImplicit oldvars) oldty
  let oldinstty = mkEmptyWildCardBndrs $ noLocA oldtysig
  let olddecl = DerivDecl EpAnnNotUsed oldinstty Nothing Nothing

  return [noLocA newdecl, noLocA olddecl]
mkDerivingGen _ = return []

-- | Create standalone deriving declaration for Shareable.
mkDerivingShare :: (TyCon, TyCon) -> TcM (Maybe (LDerivDecl GhcRn))
mkDerivingShare (_, tycon) | isVanillaAlgTyCon tycon = do
  --  Create Shareable class type and 'Nondet' type.
  sname <- tyConName <$> getShareClassTycon
  let scty = toTy sname
  mname <- tyConName <$> getMonadTycon
  let mty = toTy mname

  -- Basically the same as above.

  -- Get the lifted type constructor type.
  let tyconty = toTy (tyConName tycon)
  -- Get all type variables of the lifted type constructor.
  let vars = map fst $ visTyConTyVarsRoles tycon
  let varsname = map varName vars
  let varsty = map mkTyVarTy vars
  -- Get types of every constructor argument.
  let tys = concatMap (map (\(Scaled _ ty) -> ty) .
                           (`dataConInstArgTys` varsty)) (tyConDataCons tycon)
  -- Filter the ones that have no type variable.
  let requireds = mapMaybe (getRequired mname) tys
  -- Create a Shareable context for each remaining type.
  let ctxt = map (mkHsAppTy (mkHsAppTy scty mty)) requireds
  let clsty = mkHsAppTy scty mty
  -- Apply the class to the fully saturated lifted type constructor.
  let bdy = mkHsAppTy clsty (foldr appVars tyconty (reverse varsname))
  let ty = noLocA (HsQualTy noExtField (Just (noLocA ctxt)) bdy)
  let tysig = HsSig noExtField (HsOuterImplicit (map varName vars)) ty
  -- Include all Shareable contexts in the type and
  -- add the type variables to the set of bound variables.
  let instty = mkEmptyWildCardBndrs $ noLocA tysig
  -- Create the deriving declaration for the lifted type constructor.
  return (Just (noLocA (DerivDecl EpAnnNotUsed instty Nothing Nothing)))
mkDerivingShare _ = return Nothing

-- | Create standalone deriving declaration for Normalform.
mkDerivingNF :: (TyCon, TyCon) -> TcM (Maybe (LDerivDecl GhcRn))
mkDerivingNF (old, new) | isVanillaAlgTyCon new = do
  -- Basically the same as above again...

  nfname <- tyConName <$> getNFClassTycon
  let nfcty = toTy nfname
  mname <- tyConName <$> getMonadTycon
  let mty = toTy mname
  let newtyconty = toTy (tyConName new)
  let oldtyconty = toTy (tyConName old)
  newvarsRoles <- mapM (\(v,r) -> (,r) <$> alterVar v) $ visTyConTyVarsRoles new
  let newvars = map fst newvarsRoles
  let oldvars = map fst $ visTyConTyVarsRoles old
  let newvarsty = map mkTyVarTy newvars
  let oldvarsty = map mkTyVarTy oldvars
  let newvarsname = map varName newvars
  let oldvarsname = map varName oldvars
  let newtys = concatMap (map (\(Scaled _ ty) -> ty) .
                          (`dataConInstArgTys` newvarsty)) (tyConDataCons new)
  let oldtys = concatMap (map (\(Scaled _ ty) -> ty) .
                          (`dataConInstArgTys` oldvarsty)) (tyConDataCons old)

  -- In addition to requiring a Normalform instance for every value parameter,
  -- we also need a Normalform instance for each phanton type variable.
  -- Otherwise we run into problems with the functional dependencies of NF.
  let phanVarsNew = filter ((==Phantom) . snd) $ newvarsRoles
  let phanVarsOld = filter ((==Phantom) . snd) $ visTyConTyVarsRoles old
  let newreq = map (nlHsTyVar . varName . fst) phanVarsNew ++
               mapMaybe (getRequired mname) newtys
  let oldreq = map (nlHsTyVar . varName . fst) phanVarsOld ++
               mapMaybe (getRequired mname) oldtys

  let ctxt = zipWith (mkHsAppTy . mkHsAppTy (mkHsAppTy nfcty mty)) newreq oldreq
  let clsty = mkHsAppTy nfcty mty
  let bdy = mkHsAppTy (mkHsAppTy clsty
                (foldr appVars newtyconty (reverse newvarsname)))
                (foldr appVars oldtyconty (reverse oldvarsname))
  let ty = noLocA (HsQualTy noExtField (Just (noLocA ctxt)) bdy)
  let tysig = HsSig noExtField (HsOuterImplicit (newvarsname ++ oldvarsname)) ty
  let instty = mkEmptyWildCardBndrs $ noLocA tysig
  return (Just (noLocA (DerivDecl EpAnnNotUsed instty Nothing Nothing)))
  where
    alterVar v = do
      u <- getUniqueM
      let name = alterName u (varName v)
      return (setVarName (setVarUnique v u) name)
    alterName u n =
      let occname = occName n
          str = occNameString occname ++ "#nd"
          occname' = mkOccName (occNameSpace occname) str
      in tidyNameOcc (setNameUnique n u) occname'
mkDerivingNF _ = return Nothing

-- | Return a types its LHsType representation, without the outer Monad type.
getRequired :: Name -> Type -> Maybe (LHsType GhcRn)
getRequired tycon (TyConApp tc [ty])
  | tyConName tc == tycon = getRequired tycon ty
getRequired _ ty
  | noFreeVarsOfType ty   = Nothing
  | otherwise             = Just (typeToLHsType ty)

-- | Apply a list of type variables to a type constructor.
appVars :: Name -> LHsType GhcRn -> LHsType GhcRn
appVars n v = mkHsAppTy v (toTy n)

-- | Create a type from a given type constructor name.
toTy :: Name -> LHsType GhcRn
toTy n = noLocA (HsTyVar EpAnnNotUsed NotPromoted (noLocA n))

-- | Convert a Type to a pre-typecheck LHsType.
-- Mostly copied from GHC sources.
typeToLHsType :: Type -> LHsType GhcRn
typeToLHsType = go
  where
    go :: Type -> LHsType GhcRn
    go ty@(FunTy _ _  arg _)
      | isPredTy arg
      , (theta, tau) <- tcSplitPhiTy ty
      = noLocA (HsQualTy  { hst_ctxt = if null theta
                              then Nothing
                              else Just (noLocA (map go theta))
                          , hst_xqual = noExtField
                          , hst_body = go tau })
    go (FunTy _ _ arg res) = nlHsFunTy (go arg) (go res)
    go (ForAllTy (Bndr v vis) ty)
      = noLocA (HsForAllTy  { hst_tele = if isVisibleArgFlag vis
                                then HsForAllVis   EpAnnNotUsed [go_tv1 v]
                                else HsForAllInvis EpAnnNotUsed [go_tv2 v]
                            , hst_xforall = noExtField
                            , hst_body = go ty })
    go (AppTy t1 t2)        = nlHsAppTy (go t1) (go t2)
    go ty = noLocA (XHsType ty)

   -- Source-language types have _invisible_ kind arguments,
   -- so we must remove them here (GHC Trac #8563)

    go_tv1 :: TyVar -> LHsTyVarBndr () GhcRn
    go_tv1 tv = noLocA $ KindedTyVar EpAnnNotUsed ()
                                     (noLocA (varName tv)) (go (tyVarKind tv))

    go_tv2 :: TyVar -> LHsTyVarBndr Specificity GhcRn
    go_tv2 tv = noLocA $ KindedTyVar EpAnnNotUsed SpecifiedSpec
                                     (noLocA (varName tv)) (go (tyVarKind tv))

visTyConTyVarsRoles :: TyCon -> [(TyVar, Role)]
visTyConTyVarsRoles tc =
  mapMaybe varIfVisible (zip (tyConBinders tc) (tyConRoles tc))
  where
    varIfVisible (Bndr v (AnonTCB VisArg)                    , r) = Just (v, r)
    varIfVisible (Bndr v (NamedTCB Required)                 , r) = Just (v, r)
    varIfVisible (Bndr v (NamedTCB (Invisible SpecifiedSpec)), r) = Just (v, r)
    varIfVisible _                                                = Nothing
