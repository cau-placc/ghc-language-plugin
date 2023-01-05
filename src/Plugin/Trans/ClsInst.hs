{-|
Module      : Plugin.Trans.ClsInst
Description : Functions to handle lifting of instance information
Copyright   : (c) Kai-Oliver Prott (2020 - 2023)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift the information that GHC has
collected about a given instance.
The instance functions itself are not lifted here.
-}
module Plugin.Trans.ClsInst (liftInstance) where

import Control.Monad
import Data.Maybe

import GHC.Plugins
import GHC.Tc.Types
import GHC.Core.Class
import GHC.Core.InstEnv
import GHC.Core.Unify

import Plugin.Trans.Type
import Plugin.Trans.Class
import Plugin.Trans.Util

-- | Lift a given class instance.
liftInstance :: TyConMap -> ClsInst -> TcM ClsInst
liftInstance tcs (ClsInst _ _ origDfn tvs origCls origTys origDf ov orp) = do
  -- Lookup new class
  cls <- liftIO $ getLiftedClass origCls tcs

  -- Update type constructors
  tys <- liftIO (mapM (replaceTyconTy tcs) origTys)
  let tyc = map (fmap fst . splitTyConApp_maybe) tys
  let tyn = map mkRoughMatchTc tyc

  -- Include any shareable constraints that are required by the type variables
  -- bound in the instance head.

  -- Split the lifted type into invisible pi-types (forall, constraints) #
  -- and the rest.
  (pis, inner) <- splitInvisPiTys
    <$> liftIO (replaceTyconTy tcs (varType origDf))
  -- Get named binders (e.g., foralls).
  -- Extract variables from named binders.
  let bs = mapMaybe namedTyCoVarBinder_maybe pis
  uss <- replicateM (length bs) getUniqueSupplyM
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
      -- Function to apply the shareable type constructor to its args.
  let mkShareType t' = mkTyConApp stc [mty, t']
      -- Create Shareable constraints for all given variables.
      cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
  -- Incorporate the new constraints.
  let dfType = mkPiTys pis (foldr mkInvisFunTyMany inner cons)
  let dfLifted = setVarType origDf dfType

  -- Set other properties of the new dictionary function.
  let info' = setUnfoldingInfo (idInfo dfLifted) NoUnfolding
  let df = lazySetIdInfo dfLifted info'

  return (ClsInst (className cls) tyn origDfn tvs cls tys df ov orp)
  where
    mkRoughMatchTc (Just tc)
      | isGenerativeTyCon tc Nominal = KnownTc (tyConName tc)
    mkRoughMatchTc _                 = OtherTc
