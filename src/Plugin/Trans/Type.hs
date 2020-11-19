{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE LambdaCase          #-}
{-|
Module      : Plugin.Trans.Type
Description : Various functions to get or lift type-related things
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains our various functions to lift types and everything else
that is concerned with loading, dissecting or transforming type-related things.
-}
module Plugin.Trans.Type where

import Data.IORef
import Data.List
import Data.Maybe
import Data.Syb

import GHC.Types.Name.Occurrence hiding (varName)
import GHC.Plugins hiding (substTy, extendTvSubst)
import GHC.Unit.Finder
import GHC.Unit.External
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Instantiate
import GHC.Tc.Utils.TcType
import GHC.Tc.Utils.Env
import GHC.Iface.Syntax
import GHC.Iface.Env
import GHC.Core.Class
import GHC.Core.TyCo.Rep
import GHC.Core.Predicate

-- This Type contains an IORef, because looking up the mapping between
-- new <-> old type constructors needs IO.
-- We do not want to lookup the full mapping on plugin startup, as
-- we will probably only need a fraction of those anyway
-- | A mapping between the lifted and unlifted version of each type constructor,
-- loaded in lazily.
type TyConMap = (HscEnv, TcRef (UniqFM TyCon TyCon, -- Old -> New
                                UniqFM TyCon TyCon, -- New -> Old
                                UniqSet TyCon,       -- Old
                                UniqSet TyCon))      -- New

-- | Get the 'Nondet' monad type constructor.
getMonadTycon :: TcM TyCon
getMonadTycon = getTyCon "Plugin.Effect.Monad" "Nondet"


-- | Get the 'Shareable' class type constructor.
getShareClassTycon :: TcM TyCon
getShareClassTycon = getTyCon "Plugin.Effect.Classes" "Shareable"

-- | Get the 'Shareable' class.
getShareClass :: TcM Class
getShareClass = fromJust . tyConClass_maybe <$> getShareClassTycon

-- | Get the 'Shareable' dictionary type.
getShareClassDictType :: TcM Type
getShareClassDictType = do
  cls <- getShareClass
  let (tyvars, _, _, _) = classBigSig cls
  let clas_tyvars = snd (tcSuperSkolTyVars tyvars)
  return (mkClassPred cls (mkTyVarTys clas_tyvars))

-- | Get the 'Normalform' class type constructor.
getNFClassTycon :: TcM TyCon
getNFClassTycon = getTyCon "Plugin.Effect.Classes" "Normalform"

-- | Get the 'Generic' class type constructor.
getGenericClassTycon :: TcM TyCon
getGenericClassTycon = getTyCon "GHC.Generics" "Generic"

-- | Get a type constructor from the given module and with the given name.
getTyCon :: String    -- ^ Module name
         -> String    -- ^ TyCon name
         -> TcM TyCon
getTyCon mname name = do
  hscEnv <- getTopEnv
  Found _ mdl <- liftIO $
    findImportedModule hscEnv (mkModuleName mname) Nothing
  tcLookupTyCon =<< lookupOrig mdl ( mkTcOcc name )

{- If we have a type like (T (a -> b)), the correct lifted type is
   ND (TND (ND a -> ND b))
   Note that the function type is NOT lifted, as that lifting is integrated in
   the lifted type constructor ND
   So sometimes we do not want to lift the outermost part of a type that occurs
   somewhere nested.
   This can even occurr in more complex settings
   (T a) (a -> b) should be lifted to
   ND ((TND a) (ND a -> ND b)
   This is why we use liftInnerTy instead of liftType for nested types.

   Normally we want to add Shareable constraints to every type variable,
   using QuantifiedConstraints if possible.
   If this is undesired, use liftTypeNoShareable
-}

-- | Lift a type with the given parameters and add 'Shareable' constraints.
liftType :: TyCon       -- ^ 'Shareable' type constructor
         -> Type        -- ^ 'Nondet' type
         -> UniqSupply  -- ^ Fresh supply of unique keys
         -> TyConMap    -- ^ Type constructor map between lifted <-> unlifted
         -> Type        -- ^ Type to be lifted
         -> IO Type     -- ^ Lifted type with 'Shareable' constraints
liftType = liftTypeParametrized True

-- | Lift a type and add 'Shareable' constraints.
liftTypeTcM :: TyConMap -> Type -> TcM Type
liftTypeTcM tcs ty = do
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  liftIO (liftType stc mty us tcs ty)

-- | Lift a type with the given parameters,
-- without adding 'Shareable' constraints.
liftTypeNoShareable :: TyCon       -- ^ 'Shareable' type constructor
                    -> Type        -- ^ 'Nondet' type
                    -> UniqSupply  -- ^ Fresh supply of unique keys
                    -> TyConMap    -- ^ Type constructor map
                    -> Type        -- ^ Type to be lifted
                    -> IO Type     -- ^ Lifted type, no 'Shareable' constraints
liftTypeNoShareable = liftTypeParametrized False

-- | Lift a type with the given parameters.
-- If the first parameter is True, add 'Shareable' constraints.
liftTypeParametrized :: Bool        -- ^ Add 'Shareable' constraints or not.
                     -> TyCon       -- ^ 'Shareable' type constructor
                     -> Type        -- ^ 'Nondet' type
                     -> UniqSupply  -- ^ Fresh supply of unique keys
                     -> TyConMap    -- ^ Type constructor map
                     -> Type        -- ^ Type to be lifted
                     -> IO Type     -- ^ Lifted type
liftTypeParametrized sh stc mty s tcs t
  -- If the type is only a dictionary type, just replace type constructors.
  | isDictTy  t = replaceTyconTy tcs t
  | otherwise   = liftType' s t
  where
    liftType' :: UniqSupply -> Type -> IO Type
    liftType' us ft@(ForAllTy b ty)
      -- If we are supposed to add 'Shareable' constraints, do it.
      | sh = do
        let -- Get required fresh unique keys.
            (u1, u2) = splitUniqSupply us
            uss = listSplitUniqSupply u1
            -- Split off invisible pi-types (e.g., forall and constraints)
            (pis, inner) = splitPiTysInvisible ft
            -- Get all named binders (e.g., forall)
            named = filter isNamedBinder pis
            -- Get all bound variables
            bs = map (\(Named b') -> b') named
            -- Function to create 'Shareable' type
            mkShareType t' = mkTyConApp stc [mty, t']
            -- Make a 'Sharable' constraint for each variable
            cons = zipWith (mkShareable mkShareType) uss bs
        -- Update any type constructors of the pre-existing constraints.
        pis' <- mapM (replacePiTy tcs) pis
        -- Include 'Shareable' constraints.
        mkPiTys pis' . flip (foldr mkInvisFunTyMany) cons
          -- use the top-level version to get the isDictTy check
          <$> liftTypeParametrized sh stc mty u2 tcs inner
      | otherwise = ForAllTy b <$> liftTypeParametrized sh stc mty us tcs ty
    -- Types to the left of and invisible function type (=>) are constraints.
    liftType' us (FunTy InvisArg m ty1 ty2) =
        FunTy InvisArg m <$> replaceTyconTy tcs ty1 <*> liftType' us ty2
    -- Wrap a visible function type in our monad, except when it is a
    -- visible dictionary applictation (not possible in GHC yet).-
    liftType' us (FunTy VisArg m ty1 ty2)
      | isDictTy ty1 =
        FunTy VisArg m <$> replaceTyconTy tcs ty1 <*> liftType' us ty2
      | otherwise =
        let (u1, u2) = splitUniqSupply us
        in (mkAppTy mty .) . FunTy VisArg m <$> liftType' u1 ty1
                                            <*> liftType' u2 ty2
    liftType' us (CastTy ty kc) =
      flip CastTy kc <$> liftType' us ty
    liftType' _ (CoercionTy c) =
      return (CoercionTy c)
    liftType' _ ty@(LitTy _) =
      return (mkAppTy mty ty)
    -- Lift a type application.
    liftType' us (AppTy ty1 ty2) =
      let (u1, u2) = splitUniqSupply us
      in (mkAppTy mty .) . AppTy
           <$> liftInnerTyParametrized sh stc mty u1 tcs ty1
           <*> liftInnerTyParametrized sh stc mty u2 tcs ty2
    -- Lift a type application of a type constructor.
    -- If it is a type class constraint, do not wrap it with our monad.
    liftType' us (TyConApp tc tys)
      | isClassTyCon tc = do
        tc' <- lookupTyConMap GetNew tcs tc
        tys' <- mapM (replaceTyconTy tcs) tys
        return (TyConApp tc' tys')
      | otherwise       = do
        tc' <- lookupTyConMap GetNew tcs tc
        tys' <- mapM (liftInnerTyParametrized sh stc mty us tcs) tys
        return (mkAppTy mty (TyConApp tc' tys'))
    liftType' _ ty@(TyVarTy _) =
      return (mkAppTy mty ty)

-- | Update type constructors in a pi-type
replacePiTy :: TyConMap -> TyBinder -> IO TyBinder
replacePiTy _   (Named b              ) = return (Named b)
replacePiTy tcs (Anon  f (Scaled m t)) =
  (\m' t' -> Anon f (Scaled m' t'))
    <$> replaceTyconTy tcs m <*> replaceTyconTy tcs t

-- | Create 'Shareable' constraint for the given type variable.
mkShareable :: (Type -> Type) -> UniqSupply -> TyCoVarBinder -> Type
mkShareable mkShareType us b = mkShareableFor us mkShareType b Nothing

-- | Create 'Shareable' constraint for the given type variable and
-- add it as an invisible argument in front of the given type.
mkShareableFor :: UniqSupply -> (Type -> Type) -> TyCoVarBinder
               -> Maybe Type -> Type
mkShareableFor us mkShareType b@(Bndr v _) rest =
  let args = fst (splitFunTys (tyVarKind v))
      (u1, u2) = splitUniqSupply us
      vs = zipWith (\(Scaled _ t) -> mkTyVarWith t) args (uniqsFromSupply u1)
      bs = map (flip Bndr Inferred) vs
      vskinds = map mkTyVarTy vs
      innr = map ((. Just) . mkShareableFor u2 mkShareType) bs
      -- innr = [\ty -> ForAllTy b . (Shareable bty => ty)]
      constraint = foldr ($) (mkShareType (mkAppTys (mkTyVarTy v) vskinds)) innr
  in case rest of
    Nothing -> constraint
    Just r  -> ForAllTy b (mkInvisFunTyMany constraint r)

-- | Create a type variable with the given kind and unique key.
mkTyVarWith :: Kind -> Unique -> TyVar
mkTyVarWith k u = mkTyVar (mkSystemName u (mkTyVarOcc ("v_" ++ show u))) k

-- | Lift a type if it is not lifted already.
liftTypeIfRequired :: TyCon -> TyCon -> UniqSupply -> TyConMap -> Type
                   -> IO Type
liftTypeIfRequired stc mtycon us tcs ty =
  case splitTyConApp_maybe (snd (splitPiTysInvisible ty)) of
    -- The type might already be lifted, if this is a class method
    -- from an imported (non built-in) class
    Just (tc, _) | tc == mtycon -> replaceTyconTy tcs ty
    _                           -> liftType stc (mkTyConTy mtycon) us tcs ty

-- | Lift a type with the given arguments and
-- without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top.
liftInnerTy :: TyCon       -- ^ 'Shareable' type constructor
            -> Type        -- ^ 'Nondet' type
            -> UniqSupply  -- ^ Fresh supply of unique keys
            -> TyConMap    -- ^ Type constructor map
            -> Type        -- ^ Type to be lifted
            -> IO Type     -- ^ Lifted type with 'Shareable' constraints
liftInnerTy stc mty us tcs ty =
  snd . splitAppTy <$> liftType stc mty us tcs ty

-- | Lift a type without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top.
liftInnerTyTcM :: TyConMap -> Type -> TcM Type
liftInnerTyTcM tcs ty = do
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  liftIO (liftInnerTy stc mty us tcs ty)

-- | Lift a type without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top. The function will only add 'Shareable' constraints if
-- the first argument is True.
liftInnerTyParametrized :: Bool        -- ^ Add 'Shareable' constraints or not.
                        -> TyCon       -- ^ 'Shareable' type constructor
                        -> Type        -- ^ 'Nondet' type
                        -> UniqSupply  -- ^ Fresh supply of unique keys
                        -> TyConMap    -- ^ Type constructor map
                        -> Type        -- ^ Type to be lifted
                        -> IO Type     -- ^ Lifted type
liftInnerTyParametrized b stc mty us tcs ty
  = snd . splitAppTy <$> liftTypeParametrized b stc mty us tcs ty

-- | Lift the type of a data value constructor.
liftConType :: TyCon -> Type -> UniqSupply -> TyConMap -> Type -> IO Type
liftConType = liftConTypeWith False

-- | Lift the type of a newtype value constructor.
liftNewConType :: TyCon -> Type -> UniqSupply -> TyConMap -> Type -> IO Type
liftNewConType = liftConTypeWith True

-- When lifting the type of a constructor, we only want to lift constructor args
-- and not `->` or the result.
-- To do this, we generally do not create any applications of mty,
-- but instead switch to the normal lifting function
-- when we are to the left of an arrow.
-- For newtypes, we also do not want to wrap the constructor args,
-- so use liftInnerTy to the left of functions, if required
-- | Lift a data or newtype value constructor.
liftConTypeWith :: Bool        -- ^ Is a newtype value constructor
                -> TyCon       -- ^ 'Shareable' type constructor
                -> Type        -- ^ 'Nondet' type
                -> UniqSupply  -- ^ Fresh supply of unique keys
                -> TyConMap    -- ^ Type constructor map
                -> Type        -- ^ Type to be lifted
                -> IO Type     -- ^ Lifted type
liftConTypeWith isNew stc mty us tcs = liftType'
  where
    liftType' :: Type -> IO Type
    liftType' (ForAllTy bs ty) =
      ForAllTy bs <$> liftType' ty
    liftType' (FunTy InvisArg m ty1 ty2) =
        FunTy InvisArg m <$> replaceTyconTy tcs ty1 <*> liftType' ty2
    liftType' (FunTy VisArg m ty1 ty2)
      | isDictTy ty1 =
        FunTy VisArg m <$> replaceTyconTy tcs ty1 <*> liftType' ty2
      | isNew =
        FunTy VisArg m <$> liftInnerTy stc mty us tcs ty1 <*> liftType' ty2
      | otherwise =
        FunTy VisArg m <$> liftType stc mty us tcs ty1 <*> liftType' ty2
    liftType' (CastTy ty kc) =
      flip CastTy kc <$> liftType' ty
    liftType' (CoercionTy c) =
      return (CoercionTy c)
    liftType' (LitTy l) =
      return (LitTy l)
    liftType' (AppTy ty1 ty2) =
      AppTy <$> liftInnerTy stc mty us tcs ty1
            <*> liftInnerTy stc mty us tcs ty2
    liftType' (TyConApp tc tys) = do
      tc' <- lookupTyConMap GetNew tcs tc
      tys' <- mapM (liftInnerTy stc mty us tcs) tys
      return (TyConApp tc' tys')
    liftType' (TyVarTy v) =
      return (TyVarTy v)

-- | Replace all type constructors in a type with its lifted version.
replaceTyconTy :: TyConMap -> Type -> IO Type
replaceTyconTy tcs = replaceTyconTy'
  where
    replaceTyconTy' (ForAllTy b ty) =
      ForAllTy b <$> replaceTyconTy' ty
    replaceTyconTy' (FunTy f m ty1 ty2) =
      FunTy f m <$> replaceTyconTy' ty1 <*> replaceTyconTy' ty2
    replaceTyconTy' (CastTy ty kc) =
      flip CastTy kc <$> replaceTyconTy' ty
    replaceTyconTy' (CoercionTy c) =
      return (CoercionTy c)
    replaceTyconTy' (LitTy l) =
      return (LitTy l)
    replaceTyconTy' (AppTy ty1 ty2) =
      AppTy <$> replaceTyconTy' ty1 <*> replaceTyconTy' ty2
    replaceTyconTy' (TyConApp tc tys) = do
      tc' <- lookupTyConMap GetNew tcs tc
      tys' <- mapM (replaceTyconTy tcs) tys
      return (TyConApp tc' tys')
    replaceTyconTy' (TyVarTy v) =
      return (TyVarTy v)

replaceTyconScaled :: TyConMap -> Scaled Type -> IO (Scaled Type)
replaceTyconScaled tcs (Scaled m ty) =
  Scaled <$> replaceTyconTy tcs m <*> replaceTyconTy tcs ty

-- | Lift only the result type of a type.
-- Sometimes (e.g. for records) we only need to lift the result of a type
liftResultTy :: TyCon       -- ^ 'Shareable' type constructor
             -> Type        -- ^ 'Nondet' type
             -> UniqSupply  -- ^ Fresh supply of unique keys
             -> TyConMap    -- ^ Type constructor map
             -> Type        -- ^ Type to be lifted
             -> IO Type     -- ^ Lifted type
liftResultTy stc mty us tcs = liftResultTy'
  where
    liftResultTy' (ForAllTy b ty) =
      ForAllTy b <$> liftResultTy' ty
    liftResultTy' (FunTy f m ty1 ty2) =
      FunTy f m <$> replaceTyconTy tcs ty1 <*> liftResultTy' ty2
    liftResultTy' (CastTy ty kc) =
      flip CastTy kc <$> liftResultTy' ty
    liftResultTy' ty = liftTypeNoShareable stc mty us tcs ty

-- When lifting the type applications in a HsWrapper,
-- we have to remember that the type variables
-- (that are instantiated by this wrapper)
-- are already wrapped in the monadic type.
-- Thus, we use liftInnerTy
-- | Lift the type applications and update type constructors inside a wrapper.
-- Reomves any evidence applications.
liftWrapper :: TyCon         -- ^ 'Shareable' type constructor
             -> Type         -- ^ 'Nondet' type
             -> UniqSupply   -- ^ Fresh supply of unique keys
             -> TyConMap     -- ^ Type constructor map
             -> HsWrapper    -- ^ Wrapper to be lifted
             -> IO HsWrapper -- ^ Lifted wrapper
liftWrapper stc mty us tcs = liftWrapper'
  where
    liftWrapper' (WpCompose w1 w2) =
      WpCompose <$> liftWrapper' w1 <*> liftWrapper' w2
    liftWrapper' (WpFun w1 w2 (Scaled m ty) sd) =
      (\w1' w2' m' ty' -> WpFun w1' w2' (Scaled m' ty') sd)
            <$> liftWrapper' w1 <*> liftWrapper' w2
            <*> replaceTyconTy tcs m <*> replaceTyconTy tcs ty
    liftWrapper' (WpCast (SubCo (Refl ty))) =
      WpCast . SubCo . Refl <$> replaceTyconTy tcs ty
    liftWrapper' (WpTyApp app) =
      WpTyApp <$> liftInnerTy stc mty us tcs app
    liftWrapper' (WpTyLam v)  = return (WpTyLam v)
    -- remove any other thing that was here after typechecking
    liftWrapper' _ = return WpHole

-- | Lift the type applications and update type constructors inside a wrapper.
-- Reomves any evidence applications.
liftWrapperTcM :: TyConMap -> HsWrapper -> TcM HsWrapper
liftWrapperTcM tcs w = do
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  liftIO (liftWrapper stc mty us tcs w)

-- | Update type constructors inside a wrapper.
replaceWrapper :: TyConMap -> HsWrapper -> IO HsWrapper
replaceWrapper tcs = replaceWrapper'
  where
    replaceWrapper' (WpCompose w1 w2) =
      WpCompose <$> replaceWrapper' w1 <*> replaceWrapper' w2
    replaceWrapper' (WpFun w1 w2 (Scaled m ty) sd) =
      (\w1' w2' m' ty' -> WpFun w1' w2' (Scaled m' ty') sd)
            <$> replaceWrapper' w1 <*> replaceWrapper' w2
            <*> replaceTyconTy tcs m <*> replaceTyconTy tcs ty
    replaceWrapper' (WpCast (SubCo (Refl ty))) =
      WpCast . SubCo . Refl <$> replaceTyconTy tcs ty
    replaceWrapper' (WpTyApp app) =
      WpTyApp <$> replaceTyconTy tcs app
    replaceWrapper' (WpEvApp t) =
      WpEvApp <$> everywhereM (mkM replaceCore) t
    replaceWrapper' w =
      return w

    replaceCore v = setVarType v <$> replaceTyconTy tcs (varType v)

-- | Lift the error branch (e.g., of a missing type class implementation)
-- expression generated by GHC.
-- The error branch on a GHC error is something like
-- Control.Exception.Base.errFun @ 'GHC.Types.LiftedRep @ a "..."#.
-- Here, we want to lift the type applications, EXCEPT the LiftedRep.
liftErrorWrapper :: TyConMap -> HsWrapper -> TcM HsWrapper
liftErrorWrapper tcs (WpTyApp ty)
  | maybe True (not . isPromotedDataCon) (fst <$> splitTyConApp_maybe ty)
                         = WpTyApp <$> liftTypeTcM tcs ty
liftErrorWrapper _   w = return w

-- | Enumeration of lookup directions for the type constructor map.
data LookupDirection = GetNew -- ^ Look up the lifted version with the unlifted.
                     | GetOld -- ^ Look up the unlifted version with the lifted.
  deriving (Eq, Show)

-- | Look up the other version of a type constructor in the given map
-- or return the argument unchanged if the requested version does not exist.
-- This function lazily loads any new type constructor mappings on demand.
lookupTyConMap :: LookupDirection -> TyConMap -> TyCon -> IO TyCon
lookupTyConMap d (hsc, ref) tc = do
  -- Get the current state of our map.
  tcs@(mn, mo, sn, so) <- readIORef ref
  -- Establish the correct variables for the given lookup direction.
  let (m, s) = if d == GetNew then (mn, sn) else (mo, so)
  -- Check if we have all the infos for the given TyCon loaded already.
  if tc `elementOfUniqSet` s
    -- Look the TyCon up, with a default fallback.
    then return (lookupWithDefaultUFM m tc tc)
    -- Otherwise, get the module of the type constructor if available.
    else case mbMdl of
      -- Check if the module is in the home or external package and load it
      -- from there.
      Just mdl | toUnitId (moduleUnit mdl) == homeUnitId_ flags,
                 not (isOneShot (ghcMode flags))
                  -> tcLookupTyConHome mdl m s tcs
      _           -> tcLookupTyConExtern m s tcs
  where
    -- | Look up a type constructor replacement from a home package module.
    tcLookupTyConHome mdl m s tcs = do
      -- Get the module interface
      let miface = lookupIfaceByModule (hsc_HPT hsc) emptyPackageIfaceTable mdl
      -- Get the correct declaration to get the original name.
      case miface >>= (find declFinder . mi_decls) of
        Just (_, f) -- Look up the TyCon with the name and load it into our map.
          -> lookupType hsc (ifName f) >>= processResult m s tcs
        -- If no correct declaration was found, update our map to remember
        -- that no replacement exists.
        _ -> processResult m s tcs Nothing

    -- | Look up a type constructor replacement from an external package module.
    tcLookupTyConExtern m s tcs = do
      -- Get the table of external packages.
      ext <- eps_PTE <$> readIORef (hsc_EPS hsc)
      -- Find the correct declaration and insert the result into our map.
      let result = fmap snd (find tyThingFinder (nonDetUFMToList ext))
      processResult m s tcs result

    -- | Checks if the given declaration uses the name we are looking for.
    declFinder (_, f) = occName (ifName f) == occ2

    -- | Check if the given TyCon uses the name we are looking for.
    tyThingFinder (_, ATyCon tc') = occName n' == occ2 &&
                                      nameModule_maybe n' == mbMdl
      where n' = tyConName tc'
    tyThingFinder _               = False

    -- | Insert a lookup result into the correct map on success.
    -- Regardless of success or not, update the set of TyCons that we have
    -- performed a lookup for.
    processResult m s (mn, mo, sn, so) (Just (ATyCon tc'))
      | GetNew <- d = do
        writeIORef ref (addToUFM m tc tc', mo, addOneToUniqSet s tc, so)
        return tc'
      | otherwise   = do
        writeIORef ref (mn, addToUFM m tc tc', sn, addOneToUniqSet s tc)
        return tc'
    processResult _ s (mn, mo, sn, so) _
      | GetNew <- d = do
        writeIORef ref (mn, mo, addOneToUniqSet s tc, so)
        return tc
      | otherwise   = do
        writeIORef ref (mn, mo, sn, addOneToUniqSet s tc)
        return tc

    mbMdl = nameModule_maybe n
    flags = hsc_dflags hsc
    n = tyConName tc
    occ = occName n
    occStr = occNameString occ
    occ2 = case d of
      GetNew -> mkOccName (occNameSpace occ) (occStr ++ "ND")
      GetOld -> mkOccName (occNameSpace occ) (init (init occStr))

-- | Update the type constructors in a type with a pure,
-- side-effect free replacement map.
replaceTyconTyPure :: UniqFM TyCon TyCon -> Type -> Type
replaceTyconTyPure tcs = replaceTyconTy'
  where
    replaceTyconTy' (ForAllTy b ty) =
      ForAllTy b (replaceTyconTy' ty)
    replaceTyconTy' (FunTy f m ty1 ty2) =
      FunTy f m (replaceTyconTy' ty1) (replaceTyconTy' ty2)
    replaceTyconTy' (CastTy ty kc) =
      CastTy (replaceTyconTy' ty) kc
    replaceTyconTy' (CoercionTy c) =
      CoercionTy c
    replaceTyconTy' (LitTy l) =
      LitTy l
    replaceTyconTy' (AppTy ty1 ty2) =
      AppTy (replaceTyconTy' ty1) (replaceTyconTy' ty2)
    replaceTyconTy' (TyConApp tc tys) =
      let tc' = case lookupUFM tcs tc of
                  Just x -> x
                  _      -> tc
      in TyConApp tc' (map replaceTyconTy' tys)
    replaceTyconTy' (TyVarTy v) = TyVarTy v

-- | Remove any outer application of 'Nondet', if available.
-- Can look through type synonyms.
bindingType :: Type -> Type
bindingType (coreView -> Just ty) = bindingType ty
bindingType (TyConApp _ [ty])     = ty
bindingType ty                    = ty

-- Get only the named binders of an invisible pi-type binder.
namedTyBinders :: [TyBinder] -> [TyVarBinder]
namedTyBinders = mapMaybe (\case { Named b -> Just b; Anon _ _ -> Nothing })

-- | Instantiate a type with the given type arguments.
instantiateWith :: [Type] -> Type -> Type
instantiateWith apps ty =
  let (hd, rty) = splitPiTysInvisible ty
      isNamed (Named _) = True
      isNamed _         = False
      (named, anon) = partition isNamed hd
      vs = map binderVar (namedTyBinders named)
      subst = foldr (\(v,a) s -> extendVarEnv s v a)
        emptyTvSubstEnv (zip vs apps)
      in_scope = mkInScopeSet (tyCoVarsOfTypes (ty:apps))
  in substTy (mkTCvSubst in_scope (subst, emptyCvSubstEnv)) (mkPiTys anon rty)

-- | Create a wrapper for the given type with the provided
-- type and evidence applications.
createWrapperFor :: Type -> [Type] -> [Var] -> HsWrapper
createWrapperFor ty apps evids =
  let (hd, _) = splitPiTysInvisible ty
  in (wrapperArg hd apps evids)
  where
    wrapperArg (Named _ :xs) (a:as) evs    =
      wrapperArg xs as evs <.> WpTyApp a
    wrapperArg (Anon _ _:xs) tvs    (e:es) =
      wrapperArg xs tvs es <.> WpEvApp (EvExpr (evId e))
    wrapperArg _             _      _     =
      WpHole

createWrapperLike :: Type -> [Var] -> [Var] -> HsWrapper
createWrapperLike (ForAllTy _ ty) (v:vs) es =
  WpTyLam v <.> createWrapperLike ty vs es
createWrapperLike (FunTy InvisArg _ _ ty) vs (e:es) =
  WpEvLam e <.> createWrapperLike ty vs es
createWrapperLike _ _ _ = WpHole

collectTyDictArgs :: HsWrapper -> ([TyVar], [EvVar])
collectTyDictArgs (WpCompose w1 w2) =
  let (t1, e1) = collectTyDictArgs w1
      (t2, e2) = collectTyDictArgs w2
  in (t1 ++ t2, e1 ++ e2)
collectTyDictArgs (WpTyLam v) = ([v], [])
collectTyDictArgs (WpEvLam v) = ([], [v])
collectTyDictArgs _           = ([], [])

-- | Tries to create a wrapper of evidence applications,
-- using an entry from the type-indexed list
-- if the type matches that of the wrapper.
-- Otherwise, use one from the other list.
mkEvWrapSimilar :: HsWrapper -> [CoreExpr] -> [(Type, Var)] -> HsWrapper
mkEvWrapSimilar = go []
  where
    go _      _                 []     _             = WpHole
    go ws     (WpTyApp _  )     (v:vs) []            =
                           WpEvApp (EvExpr v)        <.> gos ws vs []
    go ws     (WpTyApp ty1)     (v:vs) ((ty2, c):cs)
      | ty1 `eqType` ty2 = WpEvApp (EvExpr (evId c)) <.> gos ws vs cs
      | otherwise        = WpEvApp (EvExpr v)        <.> gos ws vs ((ty2, c):cs)
    go ws     (WpCompose w1 w2) vs     cs            = go (w2:ws) w1 vs cs
    go ws     _                 vs     cs            = gos ws vs cs

    gos []     _  _  = WpHole
    gos (w:ws) vs cs = go ws w vs cs
