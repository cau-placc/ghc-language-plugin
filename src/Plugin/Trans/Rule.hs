module Plugin.Trans.Rule (liftRule) where

import Data.Maybe

import GHC.Hs
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Origin
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.TcType
import GHC.Tc.Utils.Monad
import GHC.Tc.Solver
import GHC.Data.Bag
import GHC.Core.Predicate

import Plugin.Trans.Expr
import Plugin.Trans.Type
import Plugin.Trans.Util

liftRule :: TyConMap -> LRuleDecl GhcTc -> TcM (LRuleDecl GhcTc)
liftRule tcs r@(L l (HsRule x nm act tvs tmvs lhs rhs)) = do
  tmvs' <- mapM (liftRuleBndr tcs) tmvs
  (lhs', constraints) <- captureConstraints (liftMonadicExpr [] tcs lhs)

  evs <- case constraints of
    WC wanted impl holes
      | isEmptyBag impl && isEmptyBag holes && allBag isWantedCt wanted
      -> return $ mapMaybe extractEvVar $ bagToList wanted
    _ -> panicAny "Lifting of rule lead to unexpected constraints" r
  let dicts = map (noLoc . RuleBndr noExtField . noLoc) evs

  lclEnv <- getLclEnv

  (L loc rhs', WC wanted impl holes) <-
    captureConstraints (liftMonadicExpr [] tcs rhs)
  let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv
  let given = listToBag $ mkGivens ctloc evs
  rhs'' <- L loc . flip mkHsWrap rhs' . mkWpLet . EvBinds <$>
    simplifyTop (WC (wanted `unionBags` given) impl holes)

  return (L l (HsRule x nm act tvs (filter isNoDict tmvs' ++ dicts) lhs' rhs''))
  where
    extractEvVar :: Ct -> Maybe Var
    extractEvVar (CQuantCan _) = Nothing
    extractEvVar ct            = case cc_ev ct of
                                  CtWanted _ (EvVarDest v) _ _
                                    -> Just v
                                  _ -> Nothing

    isNoDict :: LRuleBndr GhcTc -> Bool
    isNoDict (L _ (RuleBndr _ (L _ v))) = not $ isDictTy (varType v)
    isNoDict _                          = False

liftRuleBndr :: TyConMap -> LRuleBndr GhcTc -> TcM (LRuleBndr GhcTc)
liftRuleBndr tcs   (L l1 (RuleBndr    x (L l2 v) ))
  | isId v = L l1 . RuleBndr x . L l2 . setVarType v
                <$> liftTypeTcM tcs (varType v)
liftRuleBndr _   b@(L _  (RuleBndrSig _ _       _)) =
  panicAny "Unexpected RuleBndrSig" b
liftRuleBndr _   b = return b
