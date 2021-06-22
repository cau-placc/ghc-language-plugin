{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
{-|
Module      : Plugin.Trans.CreateSyntax
Description : Helper functions to create parts of GHC's AST
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a lot of different helper functions to create
syntactic constructs for GHC's abstract syntax tree.
-}
module Plugin.Trans.CreateSyntax where

import Language.Haskell.Syntax.Extension

import GHC.Plugins hiding (getSrcSpanM)
import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Expr
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Zonk
import GHC.Tc.Solver
import GHC.Types.Fixity
import GHC.Core.TyCo.Rep
import GHC.Core.ConLike
import GHC.Data.Bag
import GHC.Parser.Annotation

import Plugin.Trans.Constr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Trans.ConstraintSolver
import Plugin.Trans.Config
import Plugin.Effect.Classes

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
    let e = foldl ((noLocA .) . HsApp EpAnnNotUsed)
            (noLocA (wrap (HsConLikeOut noExtField (RealDataCon c))))
            (map (noLocA . HsVar noExtField . noLocA) $ reverse vs)
    -- Get the result type of the constructor.
    ty <- snd . splitFunTys <$> getTypeOrPanic e -- ok
    -- Wrap the whole term in a 'return'.
    e' <- mkApp mkNewReturnTh ty [noLocA $ HsPar EpAnnNotUsed e]
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
  ftc <- getFunTycon
  let lamty2 = mkTyConApp ftc [bindingType ty, bindingType resty] -- a --> (List a --> List a)
  -- Add a seq if C is strict in this arg
  (e', v') <- case strictness of
    HsLazy -> return (e, v)
    -- | strict or unpacked
    _      -> do
      -- create the lambda-bound variable, that needs to be shared
      v' <- freshVar vty'
      -- create share
      s <- mkApp (mkNewShareTh tcs) ty [noLocA (HsVar noExtField (noLocA v'))]
      mtycon <- getMonadTycon
      -- create seqValue
      seqE <- mkApp (mkNewSeqValueTh (bindingType ty)) (bindingType resty)
                [noLocA (HsVar noExtField (noLocA v)), e]
      let l = noLocA (HsPar EpAnnNotUsed (mkLam (noLocA v) vty' seqE resty))
      let sty = mkTyConApp mtycon [ty]
      shareE <- mkBind (noLocA (HsPar EpAnnNotUsed s)) sty l resty
      return (shareE, v')
  -- Make the lambda for this variable
  let e'' = mkLam (noLocA v') (Scaled Many ty) e' resty
  -- Wrap the whole term in a 'return'.
  e''' <- mkApp (mkNewReturnFunTh ty) resty [noLocA $ HsPar EpAnnNotUsed e'']
  let mty = mkTyConTy mtc
  return (e''', mkAppTy mty lamty2)

-- | Create a '(>>=)' for the given arguments and apply them.
mkBind :: LHsExpr GhcTc -> Type -> LHsExpr GhcTc -> Type
       -> TcM (LHsExpr GhcTc)
mkBind scr ty1 arg ty2 = do
  let ty1' = bindingType ty1
  let ty2' = bindingType ty2
  mkApp (mkNewBindTh ty1') ty2' [scr, arg]

-- | Create a 'app' for the given arguments and apply them.
mkFuncApp :: [Ct] -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc -> Type
          -> TcM (LHsExpr GhcTc)
mkFuncApp given op ty1 arg ty2 = do
  let ty1' = bindingType ty1
  let ty2' = bindingType ty2
  mkAppWith (mkNewAppTh ty1') given ty2' [op, arg]

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

-- | Create a 'return . Fun' for the given argument types.
mkNewReturnFunTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewReturnFunTh arg res = do
  ftc <- getFunTycon
  mtycon <- getMonadTycon
  let mty = mkTyConTy mtycon
  if isMonoType arg
    then do
      let expType = mkVisFunTyMany (mkVisFunTyMany arg res) $ -- (arg -> res) ->
                    mkAppTy mty (mkTyConApp ftc               -- m ((-->)
                      [ bindingType arg                       --     unM arg
                      , bindingType res ])                    --     unM res)
      ps_expr <- queryBuiltinFunctionName "rtrnFunc"
      mkNewPs ps_expr expType
    else do
      -- HACK:
      -- Since a RankN (poly type) tecnically has no monad type constructor
      -- at the outermost part of the type,
      -- we can't actually use rtrnFunc for it since that expects a function
      -- SML a -> SML b
      -- (see rtrnFuncUnsafePoly definition)
      -- Thus, we use an unsafe function.
      -- This is safe enough as long as we know that the argument is actually
      -- polymorphic when the argument is supplied at the application-site.
      -- (see mkNewAppTh)
      -- This is always the case when the function is only used in the same
      -- module, something we have to ensure anyways until RankNTypes are
      -- properly supported.
      let expType = mkVisFunTyMany (mkVisFunTyMany arg res) $ -- (arg -> res) ->
                    mkAppTy mty (mkTyConApp ftc               -- m ((-->)
                      [ arg                                   --     arg
                      , bindingType res ])                    --     unM res)
      ps_expr <- queryBuiltinFunctionName "rtrnFuncUnsafePoly"
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

-- | Create a 'app' for the given argument types.
mkNewAppTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewAppTh optype argtype = do
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  let (_, restype) = splitMyFunTy mtycon ftycon optype
  let mty = mkTyConTy mtycon
  if isMonoType argtype
    then do
      let expType = mkVisFunTyMany (mkAppTy mty optype) $ -- m optype ->
                    mkVisFunTyMany (mkAppTy mty argtype)  -- m argtype ->
                    restype                               -- restype
      ps_expr <- queryBuiltinFunctionName "app"
      mkNewPs ps_expr expType
    else do
      -- HACK:
      -- Since a RankN (poly type) tecnically has no monad type constructor
      -- at the outermost part of the type,
      -- we can't actually use app for it since that returns a function
      -- SML a -> SML b
      -- (see appUnsafePoly definition)
      -- Thus, we use an unsafe function.
      -- This is safe enough as long as we know that the function is actually
      -- polymorphic (see mkNewReturnFunTh)
      -- This is always the case when the function is only used in the same
      -- module, something we have to ensure anyways until RankNTypes are
      -- properly supported.
      let expType = mkVisFunTyMany (mkAppTy mty optype) $ -- m optype ->
                    mkVisFunTyMany argtype                -- argtype ->
                    restype                               -- restype
      ps_expr <- queryBuiltinFunctionName "appUnsafePoly"
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
  let expType = mkVisFunTyMany (mkVisFunTyMany etype btype) $ -- ('e -> 'b) ->
                mkVisFunTyMany (appMty etype) (appMty btype)  -- m 'e -> m 'b
  mkNewPs ps_expr expType

-- | Create a 'share' for the given argument types.
mkNewShareTh :: TyConMap -> Type -> TcM (LHsExpr GhcTc)
mkNewShareTh tcs ty
  | isForAllTy ty = do
    sp <- getSrcSpanM
    mtc <- getMonadTycon
    ftc <- getFunTycon
    stc <- getShareClassTycon
    let docImportant = "Cannot share polymorphic values."
    (ty', _) <- liftIO $ removeNondetShareable tcs mtc ftc stc ty
    let docSuppl = "For a variable with type" <+> ppr ty'
    e <- mkLongErrAt sp docImportant docSuppl
    reportError e
    let expType = mkVisFunTyMany ty $ -- a ->
                  mkTyConApp mtc [ty] -- m a
    u <- getUniqueM
    let nm = mkSystemName u $ mkVarOcc "share_hole"
    return (noLocA $ HsVar noExtField $ noLocA $ mkVanillaGlobal nm expType)
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
mkNewApply1 = mkNewAppTh

-- | Create a 'apply2' for the given argument types.
mkNewApply2 :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2 ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  ps_expr <- queryBuiltinFunctionName "apply2"
  let mkMyFunTy arg res = mkTyConApp ftycon [arg, res]
  let expType =
        mkVisFunTyMany (mkTyConApp mtycon              -- m (
              [mkMyFunTy ty1 (mkMyFunTy ty2 ty3)]) $   --   a --> b --> c) ->
          mkVisFunTyMany (mkTyConApp mtycon [ty1]) $   -- m a ->
            mkVisFunTyMany (mkTyConApp mtycon [ty2]) $ -- m b ->
              mkTyConApp mtycon [ty3]                  -- m c
  mkNewPs ps_expr expType

-- | Create a 'apply2Unlifted' for the given argument types.
mkNewApply2Unlifted :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2Unlifted ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  ps_expr <- queryBuiltinFunctionName "apply2Unlifted"
  let mkMyFunTy arg res = mkTyConApp ftycon [arg, res]
  let expType =
        mkVisFunTyMany (mkTyConApp mtycon            -- m (
              [mkMyFunTy ty1 (mkMyFunTy ty2 ty3)]) $ --   a --> b --> c) ->
          mkVisFunTyMany (mkTyConApp mtycon [ty1]) $ -- m a ->
            mkVisFunTyMany ty2 $                     -- b ->
              mkTyConApp mtycon [ty3]                -- m c
  mkNewPs ps_expr expType

-- | Create a '(>>=)' specialized to lists for list comprehensions.
mkListBind :: Type -> Type -> TcM SyntaxExprTc
mkListBind a b = do
  (e, constraints) <- captureConstraints (mkApp mk b [])
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  res <- zonkTopLExpr (noLocA (mkHsWrap wrapper (unLoc e)))
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
  res <- zonkTopLExpr (noLocA (mkHsWrap wrapper (unLoc e)))
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
  res <- zonkTopLExpr (noLocA (mkHsWrap wrapper (unLoc e)))
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
  res <- zonkTopLExpr (noLocA (mkHsWrap wrapper (unLoc e)))
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
  res <- zonkTopLExpr (noLocA (mkHsWrap wrapper (unLoc e)))
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
  return (noLocA (XExpr (WrapExpr (HsWrap (WpTyApp ty)
    (HsConLikeOut noExtField (RealDataCon dc))))))

-- | Create a lifted cons list constructor.
mkConsList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkConsList ty tcs = do
  dc <- liftIO (getLiftedCon consDataCon tcs)
  return (noLocA (XExpr (WrapExpr (HsWrap (WpTyApp ty)
    (HsConLikeOut noExtField (RealDataCon dc))))))


-- | Create a general lambda that binds one variable on its left side.
mkLam :: LIdP GhcTc -> Scaled Type -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc
mkLam v ty' bdy resty =
  let pat = VarPat noExtField v
      grhs = GRHS EpAnnNotUsed ([] :: [GuardLStmt GhcTc]) bdy
      rhs = GRHSs noExtField [noLoc grhs] (EmptyLocalBinds noExtField)
      match = Match EpAnnNotUsed LambdaExpr [noLocA pat] rhs
      mgtc = MatchGroupTc [ty'] resty
      mg = MG mgtc (noLocA [noLocA match]) Generated
  in noLocA $ HsPar EpAnnNotUsed $ noLocA $ HsLam noExtField mg

-- | Create a simple let expression that binds the given variable to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimpleLet :: RecFlag -> LHsExpr GhcTc -> LHsExpr GhcTc -> Var -> Type
            -> HsExpr GhcTc
mkSimpleLet f scr e v a =
  let grhs = GRHS EpAnnNotUsed [] scr
      grhss = GRHSs noExtField [noLoc grhs] (EmptyLocalBinds noExtField)
      ctxt = FunRhs (noLocA (varName v)) Prefix NoSrcStrict
      alt = Match EpAnnNotUsed ctxt [] grhss
      mgtc = MatchGroupTc [] a
      mg = MG mgtc (noLocA [noLocA alt]) Generated
      b = FunBind WpHole (noLocA v) mg []
      nbs = NValBinds [(f, listToBag [noLocA b])] []
      bs = HsValBinds EpAnnNotUsed (XValBindsLR nbs)
  in HsLet noExtField bs e

-- | Create a simple let expression that binds the given pattern to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimplePatLet :: Type -> LHsExpr GhcTc -> LPat GhcTc -> LHsExpr GhcTc
               -> HsExpr GhcTc
mkSimplePatLet ty scr p e =
  let grhs = GRHS EpAnnNotUsed [] scr
      grhss = GRHSs noExtField [noLoc grhs] (EmptyLocalBinds noExtField)
      b = PatBind ty p grhss ([], [[]])
      nbs = NValBinds [(Recursive, listToBag [noLocA b])] []
      bs = HsValBinds EpAnnNotUsed (XValBindsLR nbs)
  in HsLet noExtField bs e

-- | Create a simple (case) alternative with the given right side and patterns.
mkSimpleAlt :: HsMatchContext GhcRn -> LHsExpr GhcTc -> [LPat GhcTc]
            -> Match GhcTc (LHsExpr GhcTc)
mkSimpleAlt ctxt e ps =
  let grhs = GRHS EpAnnNotUsed [] e
      grhss = GRHSs noExtField [noLoc grhs] (EmptyLocalBinds noExtField)
  in Match EpAnnNotUsed ctxt ps grhss

-- | Create a variable pattern with the given parameter.
mkVarPat :: Var -> LPat GhcTc
mkVarPat v = noLocA (VarPat noExtField (noLocA v))

-- | Creates a let statement for the given binding.
toLetStmt :: (RecFlag, LHsBinds GhcTc) -> ExprLStmt GhcTc
toLetStmt b = noLocA (LetStmt EpAnnNotUsed bs)
  where
    bs = HsValBinds EpAnnNotUsed (XValBindsLR (NValBinds [b] []))

-- | Create a let with the given binding and inner expression.
toLetExpr :: (RecFlag, LHsBinds GhcTc) -> LHsExpr GhcTc -> LHsExpr GhcTc
toLetExpr b e = noLocA (HsLet noExtField bs e)
  where
    bs = HsValBinds EpAnnNotUsed (XValBindsLR (NValBinds [b] []))

mkHsWrap :: HsWrapper -> HsExpr GhcTc -> HsExpr GhcTc
mkHsWrap WpHole e = e
mkHsWrap w      e = XExpr (WrapExpr (HsWrap w e))

splitMyFunTy :: TyCon -> TyCon -> Type -> (Type, Type)
splitMyFunTy mtc ftc (coreView -> Just ty)    = splitMyFunTy mtc ftc ty
splitMyFunTy mtc ftc (TyConApp tc [ty1, ty2])
  | tc == ftc = (mkTyConApp mtc [ty1], mkTyConApp mtc [ty2])
  | otherwise = error $ showSDocUnsafe $ ppr (tc, ftc, ty1, ty2)
splitMyFunTy _   _   ty = error $ showSDocUnsafe $ ppr ty

{- HLINT ignore "Reduce duplication "-}
