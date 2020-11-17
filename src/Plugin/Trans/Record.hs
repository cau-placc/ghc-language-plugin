{-|
Module      : Plugin.Trans.Record
Description : Module to lift record selectors
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the function to lift the record selector function
that is introduced for each record label.
-}
{-# LANGUAGE RankNTypes #-}
module Plugin.Trans.Record (liftRecordSel) where

import Data.Typeable
import Data.Data
import Data.Tuple

import GHC.Plugins
import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Types.TypeEnv
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Data.Bag

import Plugin.Trans.Type
import Plugin.Trans.Pat
import Plugin.Trans.Constr
import Plugin.Trans.Util

-- | Lift the given record selector function, if possible.
-- Record selectors stay as a unary function after lifting and thus need
-- a lifting scheme that is different from ordinary functions.
liftRecordSel :: TyConMap -> HsBindLR GhcTc GhcTc
              -> TcM (Maybe (HsBindLR GhcTc GhcTc))
liftRecordSel tcs (AbsBinds _ tvs evs ex evb bs sig)
  | [L l (FunBind wrap _ mg ticks)] <- bagToList bs,
    [ABE _ p m w s] <- ex = do
      u <- getUniqueM
      stc <- getShareClassTycon
      us1 <- getUniqueSupplyM
      us2 <- getUniqueSupplyM

      let (parent, normalNewty) = case idDetails p of
            RecSelId (RecSelData tc)
                           _ -> (RecSelData tc,
                                isNewTyCon tc && not (isClassTyCon tc))
            RecSelId parTc _ -> (parTc, False)
            _ -> panicBndrUnsafe
                   "Expected RecSel in record selector definition" p

      -- Look up how the lifted record selector should look.
      mty <- mkTyConTy <$> getMonadTycon
      p' <- liftIO (getLiftedRecSel stc mty us1 tcs parent p)
      -- Lift its type.
      m' <- setVarType (setVarUnique (
            setVarName m (setNameUnique (varName m) u)) u)
              <$> if normalNewty
                then liftIO (replaceTyconTy tcs (varType m))
                else liftIO (liftResultTy stc mty us2 tcs (varType m))
      -- Lift its implementation.
      mg' <- liftRecSelMG normalNewty tcs m' mg

      -- Create the correct export entries and stuff.
      let selB = listToBag [L l (FunBind wrap (noLoc m') mg' ticks)]
      let ex' = ABE noExtField p' m' w s
      let b' = AbsBinds noExtField tvs evs [ex'] evb selB sig

      -- Update its type in the environment
      tenv_var <- tcg_type_env_var <$> getGblEnv
      tenv <- readTcRef tenv_var
      writeTcRef tenv_var (extendTypeEnvWithIds tenv [p'])

      return (Just b')
liftRecordSel _ _ = return Nothing

-- | Lift the MatchGroup of a record selector.
liftRecSelMG :: Bool -> TyConMap -> Var
             -> MatchGroup GhcTc (LHsExpr GhcTc)
             -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftRecSelMG normalNewty tcs f (MG (MatchGroupTc args res) (L _ alts) orig)
  = do
    args' <- liftIO (mapM (replaceTyconScaled tcs) args)
    -- Lift the result type of this match group accordingly.
    res' <- if normalNewty
      then liftIO (replaceTyconTy tcs res)
      else liftTypeTcM tcs res
    alts' <- mapM (liftRecSelAlt normalNewty tcs f) alts
    return (MG (MatchGroupTc args' res') (noLoc alts') orig)

-- | Lift an alternative of a record selector.
liftRecSelAlt :: Bool -> TyConMap -> Var -> LMatch GhcTc (LHsExpr GhcTc)
              -> TcM (LMatch GhcTc (LHsExpr GhcTc))
liftRecSelAlt normalNewty tcs f (L _ (Match _ ctxt [pat] rhs)) = do
  -- Lift any left-side pattern.
  (pat', vss, vsn) <- liftPattern tcs pat
  -- Potentially lift any unlifted newtype variables.
  let vs = if normalNewty then vsn else vss
  let ctxt' = ctxt { mc_fun = noLoc (varName f) }
  -- Replace any variables on the right side.
  -- Thankfully, a record selector is always just a single variable on the rhs.
  rhs' <- everywhere (mkT (replaceVarExpr (map swap vs)))
            <$> everywhereM (mkM (liftErrorWrapper tcs)) rhs
  return (noLoc (Match noExtField ctxt' [pat'] rhs'))
liftRecSelAlt _ _ _ x = return x

-- | Substitute variables in the given expression.
replaceVarExpr :: [(Var, Var)] -> HsExpr GhcTc -> HsExpr GhcTc
replaceVarExpr vs (HsVar _ (L l v))
  | Just v' <- lookup v vs = HsVar noExtField (L l v')
replaceVarExpr _  e        = e

everywhere :: (forall a. Data a => a -> a)
           -> (forall a. Data a => a -> a)
everywhere f = go
  where
    go :: forall a. Data a => a -> a
    go = f . gmapT go

mkT :: ( Typeable a
       , Typeable b
       )
    => (b -> b)
    -> a
    -> a
mkT = extT id

-- | Extend a generic transformation by a type-specific case
extT :: ( Typeable a
        , Typeable b
        )
     => (a -> a)
     -> (b -> b)
     -> a
     -> a
extT def ext = unT ((T def) `ext0` (T ext))

-- | The type constructor for transformations
newtype T x = T { unT :: x -> x }
