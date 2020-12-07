{-|
Module      : Plugin.Trans.ConstraintSolver
Description : Constraint solver plugin to type check imported definitions
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the constraint solver plugin that
solves any conflicts that arise from lifted imported definitions during
GHC's type checking.
This plugin is disabled automatically during lifting.
-}
module Plugin.Trans.ConstraintSolver (tcPluginSolver, removeNondet) where

import Data.Maybe
import Data.IORef
import Data.Tuple.Extra
import Control.Monad.IO.Class

import GHC.Types.Name.Occurrence
import GHC.Plugins hiding (substTy)
import GHC.Builtin.Types.Prim
import GHC.Tc.Types
import GHC.Tc.Plugin
import GHC.Tc.Types.Origin
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Core.Class
import GHC.Core.TyCo.Rep
import GHC.Core.TyCo.Subst
import GHC.Core.Unify

import Plugin.Trans.Type

-- | Constraint solver plugin to solve any conflicts that arise from
-- lifted imported definitions during GHC's type checking.
-- The first argument contains the currently known mapping of
-- lifted and unlifted type constructors.
tcPluginSolver :: IORef (UniqFM TyCon TyCon,
                         UniqFM TyCon TyCon,
                         UniqSet TyCon,
                         UniqSet TyCon)
               -> TcPluginSolver
-- Lift given constraints after unflattening phase.
tcPluginSolver m given [] []     = do
  hsc <- getTopEnv
  new <- catMaybes <$> mapM (liftGiven (hsc, m)) given
  -- The new given constraints must not be in the set of givens already.
  return (TcPluginOk [] (filter (flip all given . neqRel) new))
  where
    -- | Function to check if two given constraints are NOT equal.
    neqRel (CDictCan (CtGiven _ v _) c _ _) (CDictCan (CtGiven _ v' _) c' _ _)
               = v /= v' || c /= c'
    neqRel _ _ = True
-- Transform or solve wanted constraints after canonicalization phase.
tcPluginSolver m _     _  wanted = do
  hsc <- getTopEnv
  scls <- unsafeTcPluginTcM getShareClass
  runWantedPlugin (hsc, m) scls wanted

-- | Transform or solve wanted constraints.
-- Collects any new or solved constraints and always returns 'TcPluginOk'.
runWantedPlugin :: TyConMap -> Class -> [Ct] -> TcPluginM TcPluginResult
runWantedPlugin m cls wanteds =
  uncurry TcPluginOk . second catMaybes . unzip . catMaybes
    <$> mapM (transformWanted m cls) wanteds

-- | Transform or solve a single wanted constraint.
transformWanted :: TyConMap -> Class -> Ct
                -> TcPluginM (Maybe ((EvTerm, Ct), Maybe Ct))
-- Transform non-canonical constraints like "(Nondet t1) ~# (Nondet t2)" to
-- "t1 ~# t2" via a transformation to irreducible constraints.
-- The irreducible constraints are handled by the same function below.
transformWanted m c (CNonCanonical (CtWanted (TyConApp tc [k1, k2, ty1, ty2])
  (HoleDest (CoercionHole var _ href)) si loc))
    | tc == eqPrimTyCon = do
      res <- transformWanted m c (CIrredCan
               (CtWanted (TyConApp tc [k1, k2, ty1, ty2])
                 (HoleDest (CoercionHole var NoBlockSubst href)) si loc)
               OtherCIS)
      case res of
        Just ((EvExpr (Coercion co), (CIrredCan w' _)), Just new) ->
          return (Just ((EvExpr (Coercion co), (CNonCanonical w')), Just new))
        x -> return x
-- Transform irreducible constraints like
-- "(Nondet t1) ~# (Nondet t2)" to "t1 ~# t2".
transformWanted m _ w@(CIrredCan (CtWanted (TyConApp tc [k1, k2, ty1, ty2])
  (HoleDest (CoercionHole var _ href)) si loc) _)
    | tc == eqPrimTyCon
    = unsafeTcPluginTcM $ do
      mtc <- getMonadTycon
      stc <- getShareClassTycon
      -- Un-lift both sides of the equality.
      (ty1', b1) <- liftIO (removeNondet m mtc stc ty1)
      (ty2NoForall, b2) <- liftIO (removeNondet m mtc stc ty2)

      -- If nothing changed, try to qualify ty2 like ty1 is qualified.
      -- This is required if GHC inferred a monomorphic type
      -- for one that should be polymorph.
      (ty2', b3) <- if b1 || b2
        then return (ty2NoForall, True)
        else qualifyLike ty1' ty2NoForall

      -- As long as one of the types changed,
      -- return the constraint as solved and create a new one.
      if b3
        then do
              -- Un-lift any information about the origin of the constraint.
              origin' <- liftIO (transformOrigin m mtc stc (ctl_origin loc))
              -- Create the new IORef that will be filled with the evidence
              -- for the new equality later.
              newhref <- liftIO (newIORef Nothing)
              -- Update any information about the new constraint.
              let loc' = loc { ctl_depth  = initialSubGoalDepth
                             , ctl_origin = origin'
                            -- remove any error messages,
                            -- as they are out of date
                             , ctl_env    = (ctl_env loc) { tcl_ctxt = [] }
                             }
                  -- Create the new coercion hole for the new constraint.
                  d' = HoleDest (CoercionHole var NoBlockSubst newhref)
                  -- Create the new wanted constraint.
                  newev = CtWanted (TyConApp tc [k1, k2, ty1', ty2']) d' si loc'
                  new = CNonCanonical newev
                  -- Create the coercion that should be used as evidence for
                  -- the old constraint.
                  co = mkRepReflCo (expandTypeSynonyms ty1)
              -- Fill the old coercion hole with the new coercion.
              liftIO (writeIORef href (Just co))

              -- Return the old constraint as solved with its evidence
              -- and also return the new constraint.
              return (Just ((EvExpr (Coercion co), w), Just new))
        else return Nothing
-- Automatically solve (Shareable m a) constraints for every m and a.
transformWanted _ scls w@(CDictCan (CtWanted _ (EvVarDest v) _ _) cls _ _)
  | cls == scls = do
    evid <- newDummyEvId v
    return (Just ((EvExpr (evId evid), w), Nothing))
-- Transform a wanted type class constraint (Cls a b) to (ClsND aND bND).
transformWanted m _ w@(CDictCan (CtWanted pty (EvVarDest v) si loc) cls xi _) =
  liftClassConstraint m pty xi cls $ \pty' xi' cls' ->
    ((EvExpr (evId v), w),
     Just (CDictCan (CtWanted pty' (EvVarDest v) si loc) cls' xi' True))
transformWanted _ _ _ = return Nothing

-- | Transform a given type class constraint (ClsN aND bND) to (ClsNND aND bND).
liftGiven :: TyConMap -> Ct -> TcPluginM (Maybe Ct)
liftGiven m (CDictCan (CtGiven pty v l) cls xi _) =
  liftClassConstraint m pty xi cls $ \pty' xi' cls' ->
    CDictCan (CtGiven pty' v l) cls' xi' True
liftGiven _ _ = return Nothing

-- | Transform a type class constraint (ClsN aND bND) to (ClsNND aND bND).
liftClassConstraint :: TyConMap -> PredType -> [Type] -> Class
                    -> (PredType -> [Type] -> Class -> r)
                    -> TcPluginM (Maybe r)
liftClassConstraint m pty xi cls f = unsafeTcPluginTcM $ do
  xi' <- mapM (liftInnerTyTcM m) xi
  -- There are a few things to keep in mind here:
  -- 1. If cls is a multi parameter class (i.e. length xi /= 1), then it
  --    is defnitely not built-in.
  -- 2. If the class is NOT built-in,
  --    then there is no deterministic version of the class,
  --    except when it is defined in the current module.
  --    But then there is no nondet version.
  -- 3. If none of the types in xi change,
  --    then it mentions only type constructors from the current module.
  --    In that case, the class should not be lifted, because there will not
  --    be an instance of the required class matching the xi types.
  --    We should even unlift the class.
  -- 4. So we only swap the class to the Nondet version, iff any of the
  --    types changed. If none changed, we swap the class to the deterministic
  --    version if possible.
  -- 5. This wil not end up in a circle for unsolvable constraints, due to
  --    the class either not being built-in, or if it is built-in, the only
  --    type in xi did not change
  if not (xi `eqTypes` xi')
    then do
      Just cls' <- tyConClass_maybe
        <$> liftIO (lookupTyConMap GetNew m (classTyCon cls))
      pty' <- liftTypeTcM m pty
      return (Just (f pty' xi' cls'))
    -- If nothing in the xi type changes, we unlift the class.
    -- If that did nothing, return Nothing
    else do
      Just cls' <- tyConClass_maybe
        <$> liftIO (lookupTyConMap GetOld m (classTyCon cls))
      pty' <- liftTypeTcM m pty
      if cls /= cls'
        then return (Just (f pty' xi' cls'))
        else return Nothing

-- | Transform the origin of a constraint
-- to remove any mention of a Nondet type constructor.
transformOrigin :: TyConMap -> TyCon -> TyCon -> CtOrigin -> IO CtOrigin
transformOrigin tcs mtc stc (TypeEqOrigin act ex th vis) = do
  act' <- fst <$> removeNondet tcs mtc stc act
  ex' <- fst <$> removeNondet tcs mtc stc ex
  return (TypeEqOrigin act' ex' th vis)
transformOrigin _ _ _ o = return o

-- | Un-lift a given type. Returns the new type and True iff the type changed.
removeNondet :: TyConMap -> TyCon -> TyCon -> Type -> IO (Type, Bool)
removeNondet tcs mtc stc = removeNondet' . expandTypeSynonyms
  where
    removeNondet' (ForAllTy b ty) =
      first (ForAllTy b) <$> removeNondet' ty
    removeNondet' (FunTy InvisArg _ (TyConApp tc [_,_]) ty)
      | tc == stc =
        second (const True) <$> removeNondet' ty
    removeNondet' (FunTy f m ty1 ty2) = do
      (ty1', b1) <- removeNondet' ty1
      (ty2', b2) <- removeNondet' ty2
      return (FunTy f m ty1' ty2', b1 || b2)
    removeNondet' (CastTy ty kc) =
      first (flip CastTy kc) <$> removeNondet' ty
    removeNondet' (CoercionTy c) =
      return (CoercionTy c, False)
    removeNondet' (LitTy l) =
      return (LitTy l, False)
    removeNondet' (AppTy ty1 ty2) = do
      (ty1', b1) <- removeNondet' ty1
      (ty2', b2) <- removeNondet' ty2
      return (AppTy ty1' ty2', b1 || b2)
    removeNondet' (TyConApp tc [ty])
      | tc == mtc =
        second (const True) <$> removeNondet' ty
    removeNondet' (TyConApp tc args) = do
      (args', bs) <- unzip <$> mapM removeNondet' args
      tc' <- lookupTyConMap GetOld tcs tc
      return (TyConApp tc' args', or bs)
    removeNondet' (TyVarTy v) =
      return (TyVarTy v, False)

-- | Create a dummy variable to use in place of required evidence.
-- Note that this variable will always be out-of-scope.
-- If has to be removed before translation to core.
newDummyEvId :: Var -> TcPluginM Var
newDummyEvId v = unsafeTcPluginTcM $ do
  u <- getUniqueM
  let name = mkSystemName u (mkVarOcc "#dummy_remove")
  return $ mkLocalVar (DFunId True) name Many (varType v) vanillaIdInfo

qualifyLike :: Type -> Type -> TcM (Type, Bool)
qualifyLike (ForAllTy (Bndr v f) ty1) ty2
  | Just subst <- tcUnifyTy ty1 ty2,
    Just (TyVarTy v') <- lookupTyVar subst v,
    isTyVar v     = return (ForAllTy (Bndr v' f) (substTy subst ty2), True)
qualifyLike _ ty2 = return (ty2, False)
