{-|
Module      : Plugin.Trans.Derive
Description : Create internal derive declarations for data types
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to create deriving declarations for
a given set of lifted and unlifted type constructors.
We create deriving declarations for Generic, Shareable and Normalform.
-}
module Plugin.Trans.Derive (mkDerivings) where

import Data.Maybe

import GHC.Hs.Extension
import GHC.Hs.Types
import GHC.Hs.Decls
import GHC.Hs.Utils hiding (typeToLHsType)
import TcRnTypes
import SrcLoc
import GhcPlugins
import TyCoRep
import TcType

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
  let newvars = map varName $ tyConTyVars new
  -- Apply the class to the fully saturated lifted type constructor.
  let newbdy = mkHsAppTy clsty (foldr appVars newtyconty newvars)
  let newty = newbdy
  -- Add the type variables to the set of bound variables.
  let newinstty = mkEmptyWildCardBndrs $ HsIB newvars newty
  -- Create the deriving declaration for the lifted type constructor.
  let newdecl = DerivDecl noExtField newinstty Nothing Nothing

  -- Do the same for the old type constructor.
  let oldtyconty = toTy (tyConName old)
  let oldvars = map varName $ tyConTyVars old
  let oldbdy = mkHsAppTy clsty (foldr appVars oldtyconty oldvars)
  let oldty = oldbdy
  let oldinstty = mkEmptyWildCardBndrs $ HsIB oldvars oldty
  let olddecl = DerivDecl noExtField oldinstty Nothing Nothing

  return [noLoc newdecl, noLoc olddecl]
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
  let vars = map varName $ tyConTyVars tycon
  -- Get types of every constructor argument.
  let tys = concatMap dataConOrigArgTys (tyConDataCons tycon)
  -- Filter the ones that have no type variable.
  let requireds = mapMaybe (getRequired mname) tys
  -- Create a Shareable context for each remaining type.
  let ctxt = map (mkHsAppTy (mkHsAppTy scty mty)) requireds
  let clsty = mkHsAppTy scty mty
  -- Apply the class to the fully saturated lifted type constructor.
  let bdy = mkHsAppTy clsty (foldr appVars tyconty vars)
  -- Include all Shareable contexts in the type and
  -- add the type variables to the set of bound variables.
  let ib = HsIB vars (noLoc (HsQualTy noExtField (noLoc ctxt) bdy))
  let instty = mkEmptyWildCardBndrs ib
  -- Create the deriving declaration for the lifted type constructor.
  return (Just (noLoc (DerivDecl noExtField instty Nothing Nothing)))
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
  newvars <- mapM alterVar $ tyConTyVars new
  let oldvars = tyConTyVars old
  let newvarsty = map mkTyVarTy newvars
  let oldvarsty = map mkTyVarTy oldvars
  let newvarsname = map varName newvars
  let oldvarsname = map varName oldvars
  let newtys = concatMap (`dataConInstArgTys` newvarsty) (tyConDataCons new)
  let oldtys = concatMap (`dataConInstArgTys` oldvarsty) (tyConDataCons old)

  -- In addition to requiring a Normalform instance for every value parameter,
  -- we also need a Normalform instance for each phanton type variable.
  -- Otherwise we run into problems with the functional dependencies of NF.
  let phanVarsNew = filter ((==Phantom) . fst) $ zip (tyConRoles new) newvars
  let phanVarsOld = filter ((==Phantom) . fst) $ zip (tyConRoles old) oldvars
  let newreq = map (nlHsTyVar . varName . snd) phanVarsNew ++
               mapMaybe (getRequired mname) newtys
  let oldreq = map (nlHsTyVar . varName . snd) phanVarsOld ++
               mapMaybe (getRequired mname) oldtys

  let ctxt = zipWith (mkHsAppTy . mkHsAppTy (mkHsAppTy nfcty mty)) newreq oldreq
  let clsty = mkHsAppTy nfcty mty
  let bdy = mkHsAppTy (mkHsAppTy clsty (foldr appVars newtyconty newvarsname))
                                       (foldr appVars oldtyconty oldvarsname)
  let ty = noLoc (HsQualTy noExtField (noLoc ctxt) bdy)
  let instty = mkEmptyWildCardBndrs $ HsIB (newvarsname ++ oldvarsname) ty
  return (Just (noLoc (DerivDecl noExtField instty Nothing Nothing)))
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

-- | Check if a type contains free variables.
-- If it does, return its LHsType representation.
getRequired :: Name -> Type -> Maybe (LHsType GhcRn)
getRequired tycon ty =
  if noFreeVarsOfType ty
    then Nothing
    else Just (typeToLHsType tycon ty)

-- | Apply a list of type variables to a type constructor.
appVars :: Name -> LHsType GhcRn -> LHsType GhcRn
appVars n v = mkHsAppTy v (toTy n)

-- | Create a type from a given type constructor name.
toTy :: Name -> LHsType GhcRn
toTy n = noLoc (HsTyVar noExtField NotPromoted (noLoc n))

-- | Convert a Type to a pre-typecheck LHsType.
-- Mostly copied from GHC sources. 
typeToLHsType :: Name -> Type -> LHsType GhcRn
typeToLHsType mtc = go
  where
    go :: Type -> LHsType GhcRn
    go ty@(FunTy _ arg _)
      | isPredTy arg
      , (theta, tau) <- tcSplitPhiTy ty
      = noLoc (HsQualTy { hst_ctxt = noLoc (map go theta)
                        , hst_xqual = noExtField
                        , hst_body = go tau })
    go (FunTy _ arg res) = nlHsFunTy (go arg) (go res)
    go (ForAllTy (Bndr v vis) ty)
      = noLoc (HsForAllTy { hst_bndrs = [go_tv v]
                          , hst_xforall = noExtField
                          , hst_body = go ty
                          , hst_fvf = if isVisibleArgFlag vis
                                        then ForallVis
                                        else ForallInvis })
    go (TyVarTy tv)         = nlHsTyVar (varName tv)
    go (AppTy t1 t2)        = nlHsAppTy (go t1) (go t2)
    go (LitTy (NumTyLit n))
      = noLoc $ HsTyLit noExtField (HsNumTy NoSourceText n)
    go (LitTy (StrTyLit s))
      = noLoc $ HsTyLit noExtField (HsStrTy NoSourceText s)
    go ty@(TyConApp tc args)
      | mtc == tyConName tc, [x] <- args
      = go x
      | any isInvisibleTyConBinder (tyConBinders tc)
        -- We must produce an explicit kind signature here to make certain
        -- programs kind-check. See Note [Kind signatures in typeToLHsType].
      = noLoc $ HsKindSig noExtField lhs_ty (go (typeKind ty))
      | otherwise = lhs_ty
       where
        lhs_ty = nlHsTyConApp (tyConName tc) (map go args')
        args'  = filterOutInvisibleTypes tc args
    go (CastTy ty _)        = go ty
    go (CoercionTy co)      = pprPanic "toLHsSigWcType" (ppr co)

   -- Source-language types have _invisible_ kind arguments,
   -- so we must remove them here (GHC Trac #8563)

    go_tv :: TyVar -> LHsTyVarBndr GhcRn
    go_tv tv = noLoc $ KindedTyVar noExtField (noLoc (varName tv))
                                   (go (tyVarKind tv))
