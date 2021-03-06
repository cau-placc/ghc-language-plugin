{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plugin.Trans.CreateSyntax
Description : Helper functions to create parts of GHC's AST
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a lot of different helper functions to create
syntactic constructs for GHC's abstract syntax tree.
-}
module Plugin.Trans.CreateSyntax where

import GHC.Plugins hiding (getSrcSpanM)
import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Expr
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.Zonk
import GHC.Tc.Solver
import GHC.Types.Fixity
import GHC.Types.Error
import GHC.Core.TyCo.Rep
import GHC.Core.ConLike
import GHC.Data.Bag

import Plugin.Effect.Classes
import Plugin.Trans.Config
import Plugin.Trans.Constr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Trans.ConstraintSolver

-- | Create the lambda functions used to lift value constructors.
-- Look at their lifting for details.
mkConLam :: TyConMap -> Maybe HsWrapper -> DataCon
         -> [(Scaled Type, HsImplBang)] -> [Id] -> TcM (LHsExpr GhcTc, Type)
-- list of types is empty -> apply the collected variables.
mkConLam _ mw c [] vs = do
    -- Use the given wrapper for the constructor.
    let wrap = case mw of
          Just w  -> XExpr . WrapExpr . HsWrap w
          Nothing -> id
    -- Apply all variables in reverse to the constructor.
    let e = foldl ((noLoc .) . HsApp noExtField)
            (noLoc (wrap (HsConLikeOut noExtField (RealDataCon c))))
            (map (noLoc . HsVar noExtField . noLoc) $ reverse vs)
    -- Get the result type of the constructor.
    ty <- snd . splitFunTys <$> getTypeOrPanic e -- ok
    -- Wrap the whole term in a 'return'.
    e' <- mkApp mkNewReturnTh ty [noLoc $ HsPar noExtField e]
    mty <- mkTyConTy <$> getMonadTycon
    return (e', mkAppTy mty ty)
-- Create lambdas for the remaining types.
mkConLam tcs w c ((Scaled _ ty, strictness) : tys) vs = do
  mtc <- getMonadTycon
  -- Create the new variable to be applied to the constructor.
  let vty' = Scaled Many ty
  v <- freshVar (Scaled Many ty)
  -- Create the inner part of the term with the remaining type arguments.
  (e, resty) <- mkConLam tcs w c tys (v:vs) -- (return \xs -> Cons x xs, SML (List a -> List a)
  let lamty = mkVisFunTyMany ty resty      -- a -> SML (List a -> List a)
  -- Add a seq if C is strict in this arg
  (e', v') <- case strictness of
    HsLazy -> return (e, v)
    -- | strict or unpacked
    _      -> do
      -- create the lambda-bound variable, that needs to be shared
      v' <- freshVar vty'
      -- create share
      s <- mkApp (mkNewShareTh tcs) ty [noLoc (HsVar noExtField (noLoc v'))]
      mtycon <- getMonadTycon
      -- create seqValue
      seqE <- mkApp (mkNewSeqValueTh (bindingType ty)) (bindingType resty)
                [noLoc (HsVar noExtField (noLoc v)), e]
      let l = noLoc (HsPar noExtField (mkLam (noLoc v) vty' seqE resty))
      let sty = mkTyConApp mtycon [ty]
      shareE <- mkBind (noLoc (HsPar noExtField s)) sty l resty
      return (shareE, v')
  -- Make the lambda for this variable
  let e'' = mkLam (noLoc v') (Scaled Many ty) e' resty
  -- Wrap the whole term in a 'return'.
  e''' <- mkApp mkNewReturnTh lamty [noLoc $ HsPar noExtField e'']
  let mty = mkTyConTy mtc
  return (e''', mkAppTy mty lamty)

-- | Create the lambda to be used after '(>>=)'.
mkBindLam :: Scaled Type -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
mkBindLam (Scaled m ty) e1' = do
  let ty' = bindingType ty
  v <- noLoc <$> freshVar (Scaled m ty')
  let bdy = noLoc $ HsApp noExtField (noLoc (HsVar noExtField v)) e1'
  let (_ , _, resty) = splitFunTy (varType (unLoc v))
  return (mkLam v (Scaled m ty') bdy resty)

-- | Create a '(>>=)' for the given arguments and apply them.
mkBind :: LHsExpr GhcTc -> Type -> LHsExpr GhcTc -> Type
       -> TcM (LHsExpr GhcTc)
mkBind scr ty1 arg ty2 = do
  let ty1' = bindingType ty1
  let ty2' = bindingType ty2
  mkApp (mkNewBindTh ty1') ty2' [scr, arg]

-- | Apply the given list of arguments to a term created by the first function.
mkApp :: (Type -> TcM (LHsExpr GhcTc))
      -> Type -> [LHsExpr GhcTc]
      -> TcM (LHsExpr GhcTc)
mkApp = flip mkAppWith []

-- | Apply the given list of arguments to a term created by the first function.
-- Use the given set of given constraints to solve any wanted constraints.
mkAppWith :: (Type -> TcM (LHsExpr GhcTc))
          -> [Ct] -> Type -> [LHsExpr GhcTc]
          -> TcM (LHsExpr GhcTc)
mkAppWith con _ typ args = do
  e' <- con typ
  return $ foldl mkHsApp e' args

-- | Create a 'return' for the given argument types.
mkNewReturnTh :: Type -> TcM (LHsExpr GhcTc)
mkNewReturnTh etype = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "rtrn"
  let mty = mkTyConTy mtycon
  let expType = mkVisFunTyMany etype $ -- 'e ->
                mkAppTy mty etype  -- m 'e
  mkNewPs ps_expr expType

-- | Create a '(>>=)' for the given argument types.
mkNewBindTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewBindTh etype btype = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "bind"
  let mty = mkTyConTy mtycon
  let resty = mkAppTy mty btype
  let expType = mkVisFunTyMany (mkAppTy mty etype) $        -- m 'e ->
                mkVisFunTyMany (mkVisFunTyMany etype resty) -- (e' -> m b) ->
                  resty                                     -- m b
  mkNewPs ps_expr expType

-- | Make a seq for ordinary values (The "Prelude.seq")
mkNewSeqTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewSeqTh atype btype = do
  th_expr <- liftQ [| seq |]
  let expType = mkVisFunTyMany atype $     -- a ->
                mkVisFunTyMany btype btype -- b -> b
  mkNewAny th_expr expType

-- | Make a seq for lifted values.
mkNewSeqValueTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewSeqValueTh atype btype = do
  mtc <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "seqValue"
  let expType = mkVisFunTyMany (mkTyConApp mtc [atype]) $ -- m a ->
                mkVisFunTyMany (mkTyConApp mtc [btype])   -- m b ->
                (mkTyConApp mtc [btype])                  -- m b
  mkNewPs ps_expr expType

-- | Create a 'fmap' for the given argument types.
mkNewFmapTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewFmapTh etype btype = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "fmp"
  let appMty = mkTyConApp mtycon . (:[])
  let expType = mkVisFunTyMany (mkVisFunTyMany etype btype) $     -- ('e -> 'b) ->
                mkVisFunTyMany (appMty etype) (appMty btype)  -- m 'e -> m 'b
  mkNewPs ps_expr expType

-- | Create a 'share' for the given argument types.
mkNewShareTh :: TyConMap -> Type -> TcM (LHsExpr GhcTc)
mkNewShareTh tcs ty
  | isForAllTy ty = do
    sp <- getSrcSpanM
    ctxt <- getErrCtxt
    tidyEnv <- tcInitTidyEnv
    errrInfo <- mkErrInfo tidyEnv ctxt
    mtc <- getMonadTycon
    stc <- getShareClassTycon
    let docImportant = "Cannot share polymorphic values."
    (ty', _) <- liftIO $ removeNondetShareable tcs mtc stc ty
    let docSuppl = "For a variable with type" <+> ppr ty'
    msg <- mkErrDocAt sp (errDoc [docImportant] [docSuppl, errrInfo] [])
    reportError msg
    let expType = mkVisFunTyMany ty $ -- a ->
                  mkTyConApp mtc [ty] -- m a
    u <- getUniqueM
    let nm = mkSystemName u $ mkVarOcc "share_hole"
    return (noLoc $ HsVar noExtField $ noLoc $ mkVanillaGlobal nm expType)
  | otherwise     = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "shre"
  let expType = mkVisFunTyMany ty $    -- a ->
                mkTyConApp mtycon [ty] -- m a
  mkNewPs ps_expr expType

mkNewShareTop :: (Int, String) -> Type -> TcM (LHsExpr GhcTc)
mkNewShareTop key ty = do
  ps_expr <- queryBuiltinFunctionName "shreTopLevel"
  let tup = mkTupleTy Boxed [intTy, stringTy]
  let expType = mkVisFunTyMany tup $
                mkVisFunTyMany ty ty -- (Int, String) -> ty -> ty
  e <- mkNewPs ps_expr expType
  th_arg <- liftQ [| key |]
  arg <- mkNewAny th_arg tup
  return (mkHsApp e arg)

-- | Create a 'liftE' for the given argument types.
mkNewLiftETh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewLiftETh ty1 ty2 = do
  mty <- (. (: [])) . mkTyConApp <$> getMonadTycon
  th_expr <- liftQ [| liftE |]
  let expType = mkVisFunTyMany (mty ty1) (mty ty2) -- m a -> m b
  mkNewAny th_expr expType

-- | Create a 'nf' for the given argument types.
mkNewNfTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewNfTh ty1 ty2 = do
  mty <- (. (: [])) . mkTyConApp <$> getMonadTycon
  th_expr <- liftQ [| nf |]
  let expType = mkVisFunTyMany (mty ty1) (mty ty2) -- m a -> m b
  mkNewAny th_expr expType

-- | Create a 'apply1' for the given argument types.
mkNewApply1 :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply1 ty1 ty2 = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "apply1"
  let expType =
        mkVisFunTyMany (mkTyConApp mtycon                     -- Nondet
                  [mkVisFunTyMany (mkTyConApp mtycon [ty1])   --  ( Nondet a ->
                           (mkTyConApp mtycon [ty2])])    --    Nondet b ) ->
          (mkVisFunTyMany (mkTyConApp mtycon [ty1])           -- Nondet a ->
                   (mkTyConApp mtycon [ty2]))             -- Nondet b
  mkNewPs ps_expr expType

-- | Create a 'apply2' for the given argument types.
mkNewApply2 :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2 ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "apply2"
  let expType =
        mkTyConApp mtycon                                    -- Nondet
                  [mkVisFunTyMany (mkTyConApp mtycon [ty1])      --  (Nondet a ->
                    (mkTyConApp mtycon                       --   Nondet
                       [mkVisFunTyMany (mkTyConApp mtycon [ty2]) --     (Nondet b ->
                         (mkTyConApp mtycon [ty3])])]        --      Nondet c )
        `mkVisFunTyMany`                                         --  ) ->
        mkVisFunTyMany (mkTyConApp mtycon [ty1])                 -- Nondet a ->
          (mkVisFunTyMany (mkTyConApp mtycon [ty2])              -- Nondet b ->
                   (mkTyConApp mtycon [ty3]))                -- Nondet c
  mkNewPs ps_expr expType

-- | Create a 'apply2Unlifted' for the given argument types.
mkNewApply2Unlifted :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2Unlifted ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  ps_expr <- queryBuiltinFunctionName "apply2Unlifted"
  let expType =
        mkTyConApp mtycon                                 -- Nondet
                  [mkVisFunTyMany (mkTyConApp mtycon [ty1])      --  ( Nondet a ->
                    (mkTyConApp mtycon                    --    Nondet
                       [mkVisFunTyMany (mkTyConApp mtycon [ty2]) --      ( Nondet b ->
                         (mkTyConApp mtycon [ty3])])]     --        Nondet c )
        `mkVisFunTyMany`                                         --  ) ->
        mkVisFunTyMany (mkTyConApp mtycon [ty1])                 -- Nondet a ->
          (mkVisFunTyMany                     ty2                --        b ->
                   (mkTyConApp mtycon [ty3]))             -- Nondet c
  mkNewPs ps_expr expType

-- | Create a '(>>=)' specialized to lists for list comprehensions.
mkListBind :: Type -> Type -> TcM SyntaxExprTc
mkListBind a b = do
  (e, constraints) <- captureConstraints (mkApp mk b [])
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  res <- zonkTopLExpr (noLoc (mkHsWrap wrapper (unLoc e)))
  return (SyntaxExprTc (unLoc res) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| (>>=) |]
      let expType = mkTyConApp listTyCon [a]
                    `mkVisFunTyMany`
                    ((a `mkVisFunTyMany` mkTyConApp listTyCon [b])
                      `mkVisFunTyMany`
                      mkTyConApp listTyCon [b])
      mkNewAny th_expr expType

-- | Create a 'return' specialized to lists for list comprehensions.
mkListReturn :: Type -> TcM SyntaxExprTc
mkListReturn a = do
  (e, constraints) <- captureConstraints (mkApp mk a [])
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  res <- zonkTopLExpr (noLoc (mkHsWrap wrapper (unLoc e)))
  return (SyntaxExprTc (unLoc res) [WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| \x -> (:) x [] |]
      let expType = a `mkVisFunTyMany` mkTyConApp listTyCon [a]
      mkNewAny th_expr expType

-- | Create a 'fail' specialized to lists for list comprehensions.
mkListFail :: Type -> TcM SyntaxExprTc
mkListFail a = do
  (e, constraints) <- captureConstraints (mkApp mk a [])
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  res <- zonkTopLExpr (noLoc (mkHsWrap wrapper (unLoc e)))
  return (SyntaxExprTc (unLoc res) [WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [|  \_ -> [] |]
      let expType = stringTy `mkVisFunTyMany` mkTyConApp listTyCon [a]
      mkNewAny th_expr expType

-- | Create a 'guard' specialized to lists for list comprehensions.
mkListGuard :: TcM SyntaxExprTc
mkListGuard = do
  (e, constraints) <- captureConstraints (mkApp mk unitTy [])
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  res <- zonkTopLExpr (noLoc (mkHsWrap wrapper (unLoc e)))
  return (SyntaxExprTc (unLoc res) [WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| \b -> if b then [()] else [] |]
      let expType = boolTy `mkVisFunTyMany` mkTyConApp listTyCon [unitTy]
      mkNewAny th_expr expType

-- | Create a '(>>)' specialized to lists for list comprehensions.
mkListSeq :: Type -> Type -> TcM SyntaxExprTc
mkListSeq a b = do
  (e, constraints) <- captureConstraints (mkApp mk b [])
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  res <- zonkTopLExpr (noLoc (mkHsWrap wrapper (unLoc e)))
  return (SyntaxExprTc (unLoc res) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| (>>) |]
      let expType = mkTyConApp listTyCon [a]
                    `mkVisFunTyMany`
                    (mkTyConApp listTyCon [b]
                      `mkVisFunTyMany`
                      mkTyConApp listTyCon [b])
      mkNewAny th_expr expType

-- | Create a lifted empty list constructor.
mkEmptyList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkEmptyList ty tcs = do
  dc <- liftIO (getLiftedCon nilDataCon tcs)
  return (noLoc (XExpr (WrapExpr (HsWrap (WpTyApp ty)
    (HsConLikeOut noExtField (RealDataCon dc))))))

-- | Create a lifted cons list constructor.
mkConsList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkConsList ty tcs = do
  dc <- liftIO (getLiftedCon consDataCon tcs)
  return (noLoc (XExpr (WrapExpr (HsWrap (WpTyApp ty)
    (HsConLikeOut noExtField (RealDataCon dc))))))


-- | Create a general lambda that binds one variable on its left side.
mkLam :: Located Id -> Scaled Type -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc
mkLam v ty' bdy resty =
  let pat = VarPat noExtField v
      grhs = GRHS noExtField ([] :: [GuardLStmt GhcTc]) bdy
      rhs = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      match = Match noExtField LambdaExpr [noLoc pat] rhs
      mgtc = MatchGroupTc [ty'] resty
      mg = MG mgtc (noLoc [noLoc match]) Generated
  in noLoc $ HsPar noExtField $ noLoc $ HsLam noExtField mg

-- | Create a simple let expression that binds the given variable to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimpleLet :: RecFlag -> LHsExpr GhcTc -> LHsExpr GhcTc -> Var -> Type
            -> HsExpr GhcTc
mkSimpleLet f scr e v a =
  let grhs = GRHS noExtField [] scr
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      ctxt = FunRhs (noLoc (varName v)) Prefix NoSrcStrict
      alt = Match noExtField ctxt [] grhss
      mgtc = MatchGroupTc [] a
      mg = MG mgtc (noLoc [noLoc alt]) Generated
      b = FunBind WpHole (noLoc v) mg []
      nbs = NValBinds [(f, listToBag [noLoc b])] []
      bs = HsValBinds noExtField (XValBindsLR nbs)
  in HsLet noExtField (noLoc bs) e

-- | Create a simple let expression that binds the given pattern to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimplePatLet :: Type -> LHsExpr GhcTc -> LPat GhcTc -> LHsExpr GhcTc
               -> HsExpr GhcTc
mkSimplePatLet ty scr p e =
  let grhs = GRHS noExtField [] scr
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      b = PatBind ty p grhss ([], [[]])
      nbs = NValBinds [(Recursive, listToBag [noLoc b])] []
      bs = HsValBinds noExtField (XValBindsLR nbs)
  in HsLet noExtField (noLoc bs) e

-- | Create a simple (case) alternative with the given right side and patterns.
mkSimpleAlt :: HsMatchContext (NoGhcTc GhcTc) -> LHsExpr GhcTc -> [LPat GhcTc]
            -> Match GhcTc (LHsExpr GhcTc)
mkSimpleAlt ctxt e ps =
  let grhs = GRHS noExtField [] e
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
  in Match noExtField ctxt ps grhss

-- | Create a variable pattern with the given parameter.
mkVarPat :: Var -> LPat GhcTc
mkVarPat v = noLoc (VarPat noExtField (noLoc v))

-- | Creates a let statement for the given binding.
toLetStmt :: (RecFlag, LHsBinds GhcTc) -> ExprLStmt GhcTc
toLetStmt b = noLoc
  (LetStmt noExtField (noLoc
    (HsValBinds noExtField (XValBindsLR (NValBinds [b] [])))))

-- | Create a let with the given binding and inner expression.
toLetExpr :: (RecFlag, LHsBinds GhcTc) -> LHsExpr GhcTc -> LHsExpr GhcTc
toLetExpr b e = noLoc
  (HsLet noExtField (noLoc
    (HsValBinds noExtField (XValBindsLR (NValBinds [b] [])))) e)

mkHsWrap :: HsWrapper -> HsExpr GhcTc -> HsExpr GhcTc
mkHsWrap WpHole e = e
mkHsWrap w      e = XExpr (WrapExpr (HsWrap w e))

{- HLINT ignore "Reduce duplication "-}
