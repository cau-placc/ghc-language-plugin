{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plugin.Trans.Constr
Description : Functions to handle lifting of value constructor declarations
Copyright   : (c) Kai-Oliver Prott (2020 - 2023)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift a data or newtype
constructor declaration and
functions to get the lifted constructors and record selectors from
the type constructor map.
-}
module Plugin.Trans.Constr
  ( liftConstr, getLiftedCon, getLiftedRecSel, RecordLiftingException(..), liftRepName
  ) where

import Data.Maybe
import Data.List
import Control.Monad
import Control.Exception

import GHC.Plugins
import GHC.Types.Id.Make
import GHC.Core.TyCo.Rep
import GHC.Core.PatSyn
import GHC.Core.FamInstEnv

import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var

-- | Exception type when lifting of a class fails.
data RecordLiftingException = RecordLiftingException
    { recordWithError :: Var
    , recordSelParent :: RecSelParent
    , errorReason :: String
    }
  deriving (Eq)

instance Show RecordLiftingException where
  show (RecordLiftingException v (RecSelData tycon) s) =
    "ClassLiftingException " ++
    show (occNameString (occName v)) ++
    "(RecSelData " ++ show (occNameString (occName (tyConName tycon))) ++ ")" ++
    show s
  show (RecordLiftingException v (RecSelPatSyn syn) s) =
    "ClassLiftingException " ++
    show (occNameString (occName v)) ++
    "(RecSelData " ++ show (occNameString (occName (patSynName syn))) ++ ")" ++
    show s

instance Exception RecordLiftingException

-- | Lift a value constructor definition.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqFM' in the fifth parameter and the
-- 'TyCon' in the seventh parameter depend on the output of the computation.
liftConstr :: Bool                -- ^ True iff the type constructor should not be renamed
           -> DynFlags            -- ^ Compiler flags
           -> FamInstEnvs         -- ^ Family Instance Environments, both home and external
           -> TyCon               -- ^ 'Shareable' type constructor
           -> TyCon               -- ^ '-->' type constructor
           -> TyCon               -- ^ 'Nondet' type constructor
           -> UniqFM TyCon TyCon  -- ^ Map of old TyCon's from this module to lifted ones
           -> TyConMap            -- ^ Map of imported old TyCon's to lifted ones
           -> TyCon               -- ^ Lifted declaration type constructor
           -> UniqSupply          -- ^ Supply of fresh unique keys
           -> DataCon             -- ^ Constructor to be lifted
           -> IO DataCon          -- ^ Lifted constructor
liftConstr isClass dflags instEnvs stycon ftycon mtycon tcs tcsM tycon s cn = do

  -- Create all required unique keys.
  let (s1, tmp1) = splitUniqSupply s
      (s2, tmp2) = splitUniqSupply tmp1
      (s3, tmp3) = splitUniqSupply tmp2
      (s4, tmp4) = splitUniqSupply tmp3
      (s5, s6) = splitUniqSupply tmp4
      tmpUs = listSplitUniqSupply s4
      (uss, ss) = splitAt (length (dataConUserTyVarBinders cn)) tmpUs

  let mkShareTy ty = mkTyConApp stycon [mkTyConTy mtycon, ty]
      newSuperClassArgs
        | isClass = catMaybes $ zipWith (\u (Bndr tv _) -> Scaled Many
                                            <$> mkShareable mkShareTy u (Bndr tv Required)) uss
                              $ dataConUserTyVarBinders cn
        | otherwise = []

  -- Lift all constructor arguments and update any type constructors.
  argtys <- (newSuperClassArgs++) <$> liftIO (zipWithM liftAndReplaceType ss (dataConOrigArgTys cn))

  -- Create the new worker and constructor names, if required.
  let w        = dataConWorkId cn
      origName1 = dataConName cn
      origName2 = varName w
      (name1, name2) = if isClass
        then (origName1, origName2)
        else (liftName origName1 (uniqFromSupply s1),
              liftName origName2 (uniqFromSupply s2))

  -- Lift any record fields.
  let us = uniqsFromSupply s3
  let fs = zipWith liftField (dataConFieldLabels cn) us

  -- Update the type constructor of the constructor result.
  resty <- liftIO (replaceCon (dataConOrigResTy cn))

  let rep = case dataConWrapId_maybe cn of
              Nothing   -> NoDataConRep
              Just wrap -> initUs_ s5 $ do
                uWrap <- getUniqueM
                let wrap' = if isClass then varName wrap else
                              liftName (varName wrap) uWrap
                let bangs = dataConImplBangs cn
                mkDataConRep dflags instEnvs wrap' (Just bangs) dc
      -- Create the new constructor.
      dc = mkDataCon
        name1
        (dataConIsInfix cn)
        (maybe (tyConName $ promoteDataCon cn) (liftRepName s6) (tyConRepName_maybe tycon))
        (dataConSrcBangs cn) fs (dataConUnivTyVars cn)
        (dataConExTyCoVars cn) (dataConUserTyVarBinders cn) (dataConEqSpec cn)
        (dataConTheta cn) argtys resty NoRRI tycon
        (dataConTag cn) (dataConStupidTheta cn) worker rep
      -- let the worker be created by GHC,
      -- so that the IdInfo (especially unfolding) remains correct
      worker = mkDataConWorkId name2 dc
  return dc
  where
    mty = mkTyConTy mtycon
    liftAndReplaceType us (Scaled m ty) = Scaled <$>
          (replaceTyconTyPure tcs <$> replaceTyconTy tcsM m) <*>
          (replaceTyconTyPure tcs <$> liftType    stycon ftycon mty us tcsM ty)
    replaceCon = fmap (replaceTyconTyPure tcs) . replaceTyconTy tcsM

-- | Lift a record field by renaming its labels.
liftField :: FieldLabel -> Unique -> FieldLabel
liftField (FieldLabel str over sel selName) u = FieldLabel strND over sel selND
  where
    strND = str `appendFS` "ND"
    occND = mkOccNameFS (occNameSpace (occName selName)) strND
    selND = setNameUnique (tidyNameOcc selName occND) u

-- | Get a lifted value constructor from the given one and the TyCon map.
getLiftedCon :: DataCon -> TyConMap -> IO DataCon
getLiftedCon c tcs = do
  tc' <- lookupTyConMap GetNew tcs tc
  case midx of
    Just y -> return (tyConDataCons tc' !! y)
    _      -> return c
  where
    tc = dataConTyCon c
    midx = findIndex ((==dataConName c) . dataConName) (tyConDataCons tc)

-- | Get a lifted recrd selector from the given one and the TyCon map.
getLiftedRecSel :: TyCon        -- ^ 'Shareable' type constructor
                -> TyCon        -- ^ '-->' type constructor
                -> Type         -- ^ 'Nondet' type
                -> UniqSupply   -- ^ Fresh supply of unique keys
                -> TyConMap     -- ^ Map of imported old TyCon's to lifted ones
                -> RecSelParent -- ^ Origin of the record selector
                -> Var          -- ^ Record selector to be lifted
                -> IO Var       -- ^ Lifted record selector
getLiftedRecSel stc ftc mty us tcs (RecSelData origTc) v = do
  -- look up the lifted type constructor.
  tc' <- lookupTyConMap GetNew tcs origTc
  -- Get the index of the record selector in its original definition.
  case midx of
    Just y -> do
      -- Check if it is a newtype record.
      let normalNewty = isNewTyCon origTc && not (isClassTyCon origTc)
      -- Lift it accordingly. Note that we only want to lift the result type
      -- of the selector. It should still be a unary function.
      ty <- if normalNewty
        then replaceTyconTy tcs (varType v)
        else liftResultTy stc ftc mty us tcs (varType v)
      -- Use the index to find its new name in the new definition
      let nm = flSelector (tyConFieldLabels tc' !! y)
      return (setIdDetails (setVarName (setVarType (setVarUnique v
        (nameUnique nm)) ty) nm) (RecSelId (RecSelData tc') False))
    Nothing -> return v
  where
    midx = findIndex ((==varName v) . flSelector) (tyConFieldLabels origTc)
getLiftedRecSel _ _ _ _ _ p@(RecSelPatSyn _) v =
  throw (RecordLiftingException v p reason)
    where
      reason = "Pattern synonyms are not supported by the plugin yet"

liftRepName :: UniqSupply -> TyConRepName -> TyConRepName
liftRepName u n
  | Just mdl <- nameModule_maybe n = mkExternalName (uniqFromSupply u) mdl (mkOccName (occNameSpace (occName n)) (occNameString (occName n) ++ "ND" ++ show (uniqFromSupply u))) noSrcSpan
  | otherwise = panicAnyUnsafe "no module in repName" n
