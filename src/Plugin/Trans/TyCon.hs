{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecursiveDo   #-}
{-|
Module      : Plugin.Trans.TyCon
Description : Functions to lift type constructors.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift a type constructor,
regardless of whether or not it stems from a
class, data, type or newtype declaration.
-}
module Plugin.Trans.TyCon (liftTycon) where

import Control.Monad
import Data.Maybe

import GHC.Plugins
import GHC.Core.FamInstEnv
import GHC.Core.Coercion.Axiom

import Plugin.Trans.Constr
import Plugin.Trans.Class
import Plugin.Trans.Type
import Plugin.Trans.Var
import Plugin.Trans.Util

-- We ONLY want to keep the original version of (Data/New/Syn) definitions.
-- Thios is why we assign them a new Unique and name, while other TyCons
-- (currently only classes) get to keep their name.
-- When entering information about the new and updated TyCons into environments,
-- The new unique ensures that we do not override any information that we need
-- to keep, in contrast to the unchanged Unique for Typeclasses, etc.
-- | Lift a type constructor, if possible.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqFM' in the fourth parameter depends on the output of the computation.
liftTycon :: DynFlags            -- ^ Compiler flags
          -> FamInstEnvs         -- ^ Family Instance Environments, both home and external
          -> TyCon               -- ^ 'Shareable' type constructor
          -> TyCon               -- ^ '-->' type constructor
          -> TyCon               -- ^ Monad type constructor
          -> UniqSupply          -- ^ Fresh supply of unique keys
          -> UniqFM TyCon TyCon  -- ^ Map of old TyCon's from this module to lifted ones
          -> TyConMap            -- ^ Map of imported old TyCon's to lifted ones
          -> TyCon               -- ^ Type constructor to be lifted
          -> IO (UniqSupply, (TyCon, Maybe TyCon))
          -- ^ Next fresh unique supply, the original type constructor
          -- and maybe the lifted type constructor
liftTycon dynFlags instEnvs stycon ftycon mtycon supply tcs tcsM tc
  | isVanillaAlgTyCon tc || isClassTyCon tc = mdo
    -- The tycon definition is cyclic, so we use this let-construction.
    let (s1, tmp) = splitUniqSupply supply
        (s2, s3) = splitUniqSupply tmp
        u1 = uniqFromSupply supply
        u2 = uniqFromSupply s2
        isCls = isJust (tyConClass_maybe tc)
        monadKind = liftedTypeKind `mkVisFunTyMany` liftedTypeKind
        mVar = mkTyVar (mkInternalName u1 (mkTyVarOcc "m") noSrcSpan) monadKind
        mBinder = mkAnonTyConBinder VisArg mVar
    -- Lift the rhs of the underlying datatype definition.
    -- For classes, this lifts the implicit datatype for its dictionary.
    (us2, rhs) <- liftAlgRhs isCls dynFlags instEnvs stycon ftycon mVar mtycon tcs tcsM tycon s1
      (algTyConRhs tc)
    -- Potentially lift any class information
    flav <- case (tyConRepName_maybe tc, tyConClass_maybe tc) of
          (Just p, Just c ) -> flip ClassTyCon p <$>
            liftClass dynFlags stycon ftycon undefined tcs tcsM tycon us2 c--TODO undefined was mtycon
          (Just p, Nothing) -> return (VanillaAlgTyCon p)
          _                 ->
            panicAnyUnsafe "Unknown flavour of type constructor" tc
    -- Create the new TyCon.
    let name | isClassTyCon tc = tyConName tc
             | otherwise       = liftName (tyConName tc) u2
        tycon = mkAlgTyCon
          name (if isClassTyCon tc then tyConBinders tc else mBinder : tyConBinders tc) (tyConResKind tc)
          (if isClassTyCon tc then tyConRoles tc else Representational : tyConRoles tc) Nothing []
          rhs flav (isGadtSyntaxTyCon tc)
    return (s3, (tc, Just tycon))
  | isTypeSynonymTyCon tc = do
    let u = uniqFromSupply supply
        (supply1, supply2) = splitUniqSupply supply
    case synTyConDefn_maybe tc of
      Nothing          -> panicAnyUnsafe "Type synonym without definition" tc
      Just (_, origty) -> do
        -- lift only the "inner" type of synonyms
        ty <- replaceTyconTyPure tcs
          <$> liftInnerTy stycon ftycon undefined supply2 tcsM origty--TODO undefined was mtycon
        let name = liftName (tyConName tc) u
            tycon = mkSynonymTyCon
              name (tyConBinders tc) (tyConResKind tc)
              (tyConRoles tc) ty (isTauTyCon tc) (isFamFreeTyCon tc)
              (isForgetfulSynTyCon tc)
        return (supply1, (tc, Just tycon))
  | otherwise = return (supply, (tc, Nothing))

-- Sadly, newtype constr have to be treated differently than data constr
-- They are treated more like a type synonym, as we would end up with a double
-- nesting of the monad/nondet type.
-- Consider newtype New a = a and assume we lift this type like normal
-- to newtype NewND a = ND a.
-- Remember that at runtime, NewND and New are transparent, e.g. at runtime
-- each occurrence of NewND and New is de-facto removed.
-- Thus, if we look at a funcion type
-- test :: New a -> a, its lifted version is test :: ND (NewND a) --> ND a.
-- If we were to treat NewND as we said above, at runtime test would
-- have effectively the following signature:
-- test :: ND (ND a) --> ND a, which has one application of ND too much.
-- Thus, we use the lifting of type synonyms for newtypes, as that gets rid
-- of the inner ND application.
-- BUT for the newtypes that represent dictionaries for class definitions,
-- we have to use the normal constructor lifting.
-- This is required, because the argument of that newtype is the same as
-- the type of the function from the typeclass. The function type gets
-- lifted normally, and so we do the same with the newtype constructor.
-- (At least without kind polymorphism), a Class cannot occur nested inside of
-- another type like in the example with test.
-- So the special treatment of newtype constructors for classes
-- does not result in any (further) problems.
-- | Lift the right hand side of a type constructor.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqFM' in the fourth parameter and the
-- 'TyCon' in the sixth parameter depend on the output of the computation.
liftAlgRhs :: Bool                -- ^ Is it a class definition or not
           -> DynFlags            -- ^ Compiler flags
           -> FamInstEnvs         -- ^ Family Instance Environments, both home and external
           -> TyCon               -- ^ 'Shareable' type constructor
           -> TyCon               -- ^ '-->' type constructor
           -> Var                 -- ^ 'Monad' type variable
           -> TyCon               -- ^ 'Monad' type constructor
           -> UniqFM TyCon TyCon  -- ^ Map of old TyCon's from this module to lifted ones
           -> TyConMap            -- ^ Map of imported old TyCon's to lifted ones
           -> TyCon               -- ^ Lifted TyCon of this rhs
           -> UniqSupply          -- ^ Fresh supply of unique keys
           -> AlgTyConRhs         -- ^ Rhs to be lifted
           -> IO (UniqSupply, AlgTyConRhs)
          -- ^ Next fresh unique key supply and lifted rhs
liftAlgRhs isClass dflags instEnvs stycon ftycon mvar mtycon tcs tcsM tycon us
  -- Just lift all constructors of a data decl.
  (DataTyCon cns size ne) = case listSplitUniqSupply us of
    []      -> panicAnyUnsafe "Finite Unique supply" ()
    (u:uss) -> do
      cns' <- zipWithM (liftConstr isClass dflags instEnvs stycon ftycon mvar mtycon tcs tcsM tycon) uss cns
      return (u, DataTyCon cns' size ne)
liftAlgRhs isClass dflags instEnvs stycon ftycon mvar mtycon tcs tcsM tycon us
  -- Depending on the origin of this newtype declaration (class or not),
  -- Perform a full lifting or just and inner lifting.
  (NewTyCon dc rhs _ co lev) = do
    let (u1, tmp1) = splitUniqSupply us
        (u2, tmp2) = splitUniqSupply tmp1
        (u3, u4  ) = splitUniqSupply tmp2
    dc' <- liftConstr isClass dflags instEnvs stycon ftycon mvar mtycon tcs tcsM tycon u1 dc
    let mtype = if isClass then mkTyConTy mtycon else mkTyVarTy mvar
    rhs' <- replaceTyconTyPure tcs <$> liftType stycon ftycon mtype u2 tcsM rhs

    -- Only switch unique and name for datatypes, etc.
    -- (see comment above liftTycon)
    let u = if isClass then co_ax_unique co else uniqFromSupply u3
    let axName = co_ax_name co
    let axNameNew | isClass   = setNameUnique axName u
                  | otherwise = liftName axName u

    let (vars, roles) = if isClass then (tyConTyVars tycon, tyConRoles tycon)
                                   else (mvar : tyConTyVars tycon, Representational : tyConRoles tycon)
    -- Create new coercion axiom.
    let (etavs, etaroles, etarhs) = eta_reduce (reverse vars) (reverse roles) rhs'
    let co' = mkNewTypeCoAxiom axNameNew tycon etavs etaroles etarhs
    return (u4, NewTyCon dc' rhs' (etavs, etarhs) co' lev)
liftAlgRhs _ _ _ _ _ _ _ _ _ _ u c = return (u, c)

-- | Eta-reduce type variables of a newtype declaration to generate a
-- more siple newtype coercion.
-- Copied from GHC.Tc.TyCl.Build
eta_reduce :: [TyVar]       -- ^ Reversed list of type variables
           -> [Role]        -- ^ Reversed list of their roles
           -> Type          -- ^ Type of the rhs
           -> ([TyVar], [Role], Type)  -- ^ Eta-reduced type
                                       -- (tyvars in normal order)
eta_reduce (a:as) (_:rs) ty | Just (fun, arg) <- splitAppTy_maybe ty,
                              Just tv <- getTyVar_maybe arg,
                              tv == a,
                              not (a `elemVarSet` tyCoVarsOfType fun)
                            = eta_reduce as rs fun
eta_reduce tvs rs ty = (reverse tvs, reverse rs, ty)
