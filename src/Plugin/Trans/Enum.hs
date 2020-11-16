{-|
Module      : Plugin.Trans.Enum
Description : Functions to detect and lift derived 'Enum' instances
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains everything required to detect if an 'Enum' instance is
derived and a function to lift those instances.
'Enum' instances derived by GHC are special and use a lifting scheme that is
different from all other type classes.
-}
module Plugin.Trans.Enum
  ( isDerivedEnumBind, isDerivedEnum
  , liftDerivedEnumEquation
  ) where

import Data.List

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Expr
import SrcLoc
import GhcPlugins
import Bag
import TcRnMonad

import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.CreateSyntax

-- | Check if a given binding is an instance function created by a
-- GHC deriving clause for 'Enum'.
isDerivedEnumBind :: HsBindLR GhcTc GhcTc -> Bool
isDerivedEnumBind (FunBind _ _ eqs _ _) =
  isDerivedEnum eqs
isDerivedEnumBind (AbsBinds _ _ _ _ _ bs _) =
  anyBag (isDerivedEnumBind . unLoc) bs
isDerivedEnumBind _ = False

-- | Check if a given MatchGroup is from an instance function created by a
-- GHC deriving clause for 'Enum'.
-- A function of a derived enum instance (after pattern matching)
-- that needs a different lifting due to its usage of unboxed integers is:
-- 1. a zero arity MatchGroup with one equation
-- 3. and no guards
-- 3. with a body that starts with any number of lambdas
-- 4. which are then followed by either:
--    4.a A let expression that binds a variable to "($con2tag_X v)"
--    5.b An if-expression that has $tag2con_X v in one of its branches
isDerivedEnum :: MatchGroup GhcTc (LHsExpr GhcTc) -> Bool
isDerivedEnum (MG (MatchGroupTc [] _) (L _ [L _ (Match _ _ []            -- 1.
                 (GRHSs _ [L _ (GRHS _ [] e)] _))]) _) =                 -- 2.
  case unLoc (getBodyExpr e) of                                          -- 3.
    HsLet _ (L _ (HsValBinds _ (XValBindsLR (NValBinds [(_, bs)] _)))) _
      | [L _ (FunBind _ _ (MG _ (L _ [L _ (Match _ _ [] (GRHSs _
          [L _ (GRHS _ [] (L _ (HsPar _ e1)))] _))]) _) _ _)] <- bagToList bs
                     -> isDerivedEnumExpr "$con2tag_" e1                 -- 4.a
    HsIf _ _ _ e1 e2 -> any (isDerivedEnumExpr "$tag2con_") [e1, e2]     -- 4.b
    _                -> False
isDerivedEnum _ = False

-- | Check if the given expression is a call to a function that matches the
-- given name.
isDerivedEnumExpr :: String -> LHsExpr GhcTc -> Bool
isDerivedEnumExpr name (L _ (HsApp _ (L _ (HsVar _ (L _ v))) _)) =
  name `isPrefixOf` occNameString (occName v)
isDerivedEnumExpr _ _ = False

-- | Lift a given MatchGroup that stems from an instance function created by a
-- GHC deriving clause for 'Enum'.
liftDerivedEnumEquation :: TyConMap -> MatchGroup GhcTc (LHsExpr GhcTc)
                        -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftDerivedEnumEquation tcs (MG (MatchGroupTc [] res) (L b alts) c) = do
  alts' <- mapM (liftDerivedEnumAlt tcs) alts
  res' <- liftTypeTcM tcs res
  return (MG (MatchGroupTc [] res') (L b alts') c)
liftDerivedEnumEquation _ a = return a

-- | Lift a given rule that stems from an instance function created by a
-- GHC deriving clause for 'Enum'.
liftDerivedEnumAlt :: TyConMap -> LMatch GhcTc (LHsExpr GhcTc)
                   -> TcM (LMatch GhcTc (LHsExpr GhcTc))
liftDerivedEnumAlt tcs (L a (Match b c [] rhs)) = do
  rhs' <- liftDerivedEnumRhs tcs rhs
  return (L a (Match b c [] rhs'))
liftDerivedEnumAlt _ a = return a

-- | Lift a given right side of a rule
-- that stems from an instance function created by a
-- GHC deriving clause for 'Enum'.
liftDerivedEnumRhs :: TyConMap -> GRHSs GhcTc (LHsExpr GhcTc)
                   -> TcM (GRHSs GhcTc (LHsExpr GhcTc))
liftDerivedEnumRhs tcs (GRHSs a grhs b) = do
  grhs' <- mapM (liftDerivedEnumGRhs tcs) grhs
  return (GRHSs a grhs' b)
liftDerivedEnumRhs _ a = return a

-- | Lift a given guarded right side of a rule
-- that stems from an instance function created by a
-- GHC deriving clause for 'Enum'.
liftDerivedEnumGRhs :: TyConMap -> LGRHS GhcTc (LHsExpr GhcTc)
                    -> TcM (LGRHS GhcTc (LHsExpr GhcTc))
liftDerivedEnumGRhs tcs (L a (GRHS b c body)) =
  L a . GRHS b c <$> liftDerivedEnumExpr tcs body
liftDerivedEnumGRhs _ a = return a


-- | Lift a given expression that stems from an instance function created by a
-- GHC deriving clause for 'Enum'.
-- The lifting uses the following set of rules:
-- 1. \v -> e
--    ~> return (\v' -> nf v' >>= \v -> e')
-- 2. (e)
--    ~> (e')
-- 3. e
--    ~> liftE (return e)
liftDerivedEnumExpr :: TyConMap -> LHsExpr GhcTc
                    -> TcM (LHsExpr GhcTc)
liftDerivedEnumExpr tcs (L l1 (HsLam x1 (MG (MatchGroupTc [arg] res) (L l2
  [L l3 (Match x2 ctxt [L l4 (VarPat x3 (L l5 v))]
  (GRHSs x4 [L l6 (GRHS x5 g e)] lcl))]) orig))) = do
    -- create the new pattern variable
    u <- getUniqueM
    vty <- liftTypeTcM tcs (varType v)
    let v' = setVarType (setVarUnique v u) vty
    -- lift the remaining expression
    e' <- liftDerivedEnumExpr tcs e
    -- bind the old variable again
    e'' <- mkNFVar v' v e'
    -- lift the type of this lambda
    arg' <- liftTypeTcM tcs arg
    res' <- liftTypeTcM tcs res
    -- create the lambda
    let e''' = L l1 (HsLam x1 (MG (MatchGroupTc [arg'] res') (L l2
                 [L l3 (Match x2 ctxt [L l4 (VarPat x3 (L l5 v'))]
                 (GRHSs x4 [L l6 (GRHS x5 g e'')] lcl))]) orig))
    let ty = mkVisFunTyMany arg' res'
    mkApp mkNewReturnTh ty [noLoc (HsPar noExtField e''')]
liftDerivedEnumExpr tcs (L l (HsPar x e)) =
  L l . HsPar x <$> liftDerivedEnumExpr tcs e
liftDerivedEnumExpr tcs e = do
  ty <- getTypeOrPanic e
  lifted <- mkApp mkNewReturnTh ty [e]
  ty' <- liftIO (replaceTyconTy tcs ty)
  mkApp (mkNewLiftETh ty) ty' [lifted]

-- | Create the following expression:
-- nf vn >>= \vo -> e
mkNFVar :: Var -> Var -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
mkNFVar vn vo e = do
  let vne = noLoc (HsVar noExtField (noLoc vn))
  let vnty = varType vn
  let voty = varType vo
  s <- mkApp (mkNewNfTh (bindingType vnty)) voty [vne]
  ety <- getTypeOrPanic e
  let l = noLoc (HsPar noExtField (mkLam (noLoc vo) voty e ety))
  mtc <- getMonadTycon
  mkBind s (mkTyConApp mtc [voty]) l ety

-- | Get the result expression that might be nested behind a lot of
-- lambda abstractions.
getBodyExpr :: LHsExpr GhcTc -> LHsExpr GhcTc
getBodyExpr (L _ (HsLam _ (MG _ (L _ [L _ (Match _ _ _
  (GRHSs _ [L _ (GRHS _ _ e)] _))]) _))) = getBodyExpr e
getBodyExpr e = e
