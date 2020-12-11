module Plugin.Trans.Rule (liftRule) where

import Data.Maybe

import GHC.Hs
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Tc.Types.Constraint
import GHC.Tc.Solver
import GHC.Tc.Solver.Monad
import GHC.Data.Bag

import Plugin.Trans.Expr
import Plugin.Trans.Type
import Plugin.Trans.Util

liftRule :: TyConMap -> LRuleDecl GhcTc -> TcM (LRuleDecl GhcTc)
liftRule tcs r@(L l (HsRule x nm act tvs tmvs lhs rhs)) = do
  tmvs' <- mapM (liftRuleBndr tcs) tmvs
  ((lhs', rhs'), constraints)
    <- captureConstraints ((,) <$> liftMonadicExpr [] tcs lhs
                               <*> liftMonadicExpr [] tcs rhs)

  (simplified, _) <- runTcS (solveWantedsAndDrop constraints >>= zonkWC)

  dicts <- case simplified of
    WC wanted impl holes
      | isEmptyBag impl && isEmptyBag holes && allBag isWantedCt wanted
      -> return $ mapMaybe extractEvVar $ bagToList wanted
    _ -> panicAny "Lifting of rule lead to unexpected constraints" r

  return (L l (HsRule x nm act tvs (tmvs' ++ dicts) lhs' rhs'))
  where
    extractEvVar :: Ct -> Maybe (LRuleBndr GhcTc)
    extractEvVar (CQuantCan _) = Nothing
    extractEvVar ct            = case cc_ev ct of
      CtWanted _ (EvVarDest v) _ _
        -> Just (noLoc (RuleBndr noExtField (noLoc v)))
      _ -> Nothing

liftRuleBndr :: TyConMap -> LRuleBndr GhcTc -> TcM (LRuleBndr GhcTc)
liftRuleBndr tcs   (L l1 (RuleBndr    x (L l2 v) ))
  | isId v = L l1 . RuleBndr x . L l2 . setVarType v
                <$> liftTypeTcM tcs (varType v)
liftRuleBndr _   b@(L _  (RuleBndrSig _ _       _)) =
  panicAny "Unexpected RuleBndrSig" b
liftRuleBndr _   b = return b
