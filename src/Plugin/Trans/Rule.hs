module Plugin.Trans.Rule (liftRule) where

import Data.Maybe
import Control.Monad

import GHC.Hs
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.TcType
import GHC.Tc.Types.Origin
import GHC.Tc.Types.Constraint

import Plugin.Trans.Expr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var

liftRule :: TyConMap -> LRuleDecl GhcTc -> TcM (LRuleDecl GhcTc)
liftRule tcs (L l (HsRule x nm act tvs tmvs lhs rhs)) = do
  let vs = mapMaybe maybeTyvar tmvs

  -- create the dictionary variables
  stc <- getShareClassTycon
  mty <- mkTyConTy <$> getMonadTycon
  uss <- replicateM (length vs) getUniqueSupplyM
  let mkShareTy ty = mkTyConApp stc [mty, ty]
  let evsty = catMaybes $
              zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss vs
  evs <- mapM freshDictId evsty
  lclEnv <- getLclEnv
  let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv
  let cts = mkGivens ctloc evs
  let evsbndr = map (noLoc . RuleBndr noExtField . noLoc) evs

  tmvs' <- mapM (liftRuleBndr tcs) tmvs
  lhs' <- liftMonadicExpr cts tcs lhs
  rhs' <- liftMonadicExpr cts tcs rhs

  return (L l (HsRule x nm act tvs (evsbndr ++ tmvs') lhs' rhs'))
  where
    maybeTyvar :: LRuleBndr GhcTc -> Maybe Id
    maybeTyvar (L _ (RuleBndr _ (L _ v)))
      | isTyVar v = Just v
    maybeTyvar _  = Nothing

liftRuleBndr :: TyConMap -> LRuleBndr GhcTc -> TcM (LRuleBndr GhcTc)
liftRuleBndr tcs   (L l1 (RuleBndr    x (L l2 v) ))
  | isId v = L l1 . RuleBndr x . L l2 . setVarType v
                <$> liftTypeTcM tcs (varType v)
liftRuleBndr _   b@(L _  (RuleBndrSig _ _       _)) =
  panicAny "Unexpected RuleBndrSig" b
liftRuleBndr _   b = return b
