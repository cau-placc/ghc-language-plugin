{-|
Module      : Plugin.Trans.ClsInst
Description : Functions to handle lifting of instance information
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift the information that GHC has
collected about a given instance.
The instance functions itself are not lifted here.
-}
module Plugin.Trans.ClsInst (liftInstance) where

import Control.Monad

import GhcPlugins
import Class
import InstEnv
import TcRnTypes
import TyCoRep

import Plugin.Trans.Type
import Plugin.Trans.Class

-- | Lift a given class instance.
liftInstance :: TyConMap -> ClsInst -> TcM ClsInst
liftInstance tcs (ClsInst _ _ origDfn tvs origCls origTys origDf ov orp) = do
  -- Lookup new class
  cls <- liftIO $ getLiftedClass origCls tcs

  -- Update type constructors
  tys <- liftIO (mapM (replaceTyconTy tcs) origTys)
  let tyn = map (fmap (tyConName . fst) . splitTyConApp_maybe) tys

  -- Include any shareable constraints that are required by the type variables
  -- bound in the instance head.

  -- Split the lifted type into invisible pi-types (forall, constraints) #
  -- and the rest.
  (pis, inner) <- splitPiTysInvisible
    <$> liftIO (replaceTyconTy tcs (varType origDf))
  -- Get named binders (e.g., foralls).
  let named = filter isNamedBinder pis
  uss <- replicateM (length named) getUniqueSupplyM
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
  let -- Extract variables from named binders.
      bs = map (\(Named b') -> b') named
      -- Function to apply the shareable type constructor to its args.
      mkShareType t' = mkTyConApp stc [mty, t']
      -- Create Shareable constraints for all given variables.
      cons = zipWith (mkShareable mkShareType) uss bs
  -- Incorporate the new constraints.
  let dfType = mkPiTys pis (foldr mkInvisFunTy inner cons)
  let dfLifted = setVarType origDf dfType

  -- Set other properties of the new dictionary function.
  let info' = setUnfoldingInfo (idInfo dfLifted) NoUnfolding
  let df = lazySetIdInfo dfLifted info'

  return (ClsInst (className cls) tyn origDfn tvs cls tys df ov orp)
