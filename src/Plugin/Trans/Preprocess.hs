{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plugin.Trans.Preprocess
Description : Simplify functions to prepare for lifting
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module simplifies functions to prepare them for the lifting phase.
At its core, this phase simplifies pattern matching and does a few minor
rewrites of selected expressions.
-}
module Plugin.Trans.Preprocess (preprocessBinding) where

import Data.Syb

import GHC.Plugins
import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Expr
import GHC.Hs.Pat
import GHC.Hs.Lit
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Utils.Error

import Plugin.Trans.Util
import Plugin.Trans.PatternMatching

-- | Preprocess a binding before lifting, to get rid of nested pattern matching.
-- Also removes some explicit type applications and fuses HsWrapper.
preprocessBinding :: Bool -> HsBindLR GhcTc GhcTc -> TcM (HsBindLR GhcTc GhcTc)
preprocessBinding lcl (AbsBinds a b c d e f g)
  -- Record selectors should stay like they are for now.
  | not (any (isRecordSelector . abe_poly) d) = do
  -- Rreprocess each binding seperate.
  bs <- liftBag (preprocessBinding lcl) f
  return (AbsBinds a b c d e bs g)
preprocessBinding lcl (FunBind a (L b name) eqs ticks) = do
  -- Compile pattern matching first, but only use matchExpr
  -- if this is a top-level binding to avoid doing this multiple times.
  Left matchedGr <- compileMatchGroup eqs
  matched <- (if lcl then return else everywhereM (mkM matchExpr)) matchedGr
  -- Preprocess the inner part of the declaration afterwards.
  eqs' <- preprocessEquations matched
  return (FunBind a (L b name) eqs' ticks)
preprocessBinding _ a = return a

preprocessEquations :: MatchGroup GhcTc (LHsExpr GhcTc)
                    -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
preprocessEquations (MG a (L b alts) c) = do
  alts' <- mapM preprocessAlt alts
  return (MG a (L b alts') c)

preprocessAlt :: LMatch GhcTc (LHsExpr GhcTc)
              -> TcM (LMatch GhcTc (LHsExpr GhcTc))
preprocessAlt (L a (Match b c d rhs)) = do
  rhs' <- preprocessRhs rhs
  return (L a (Match b c d rhs'))

preprocessRhs :: GRHSs GhcTc (LHsExpr GhcTc)
              -> TcM (GRHSs GhcTc (LHsExpr GhcTc))
preprocessRhs (GRHSs a grhs b) = do
  grhs' <- mapM preprocessGRhs grhs
  return (GRHSs a grhs' b)

preprocessGRhs :: LGRHS GhcTc (LHsExpr GhcTc)
               -> TcM (LGRHS GhcTc (LHsExpr GhcTc))
preprocessGRhs (L a (GRHS b c body)) = do
  body' <- preprocessExpr body
  return (L a (GRHS b c body'))

-- preprocessExpr traverses the AST to reach all local function definitions
-- and removes some ExplicitTypeApplications.
-- Some HsWrapper might be split into two halves on each side of an
-- explicit type applications. We have to fuse those wrappers.
preprocessExpr :: LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
preprocessExpr (L l (XExpr (WrapExpr (HsWrap w1
                 (HsAppType _ (L _ (XExpr (WrapExpr (HsWrap w2 e)))) _))))) =
  return (L l (XExpr (WrapExpr (HsWrap (w1 <.> w2) e))))
preprocessExpr e@(L _ (HsVar _ (L _ _))) =
  return e
preprocessExpr e@(L _ HsLit{}) =
  return e
preprocessExpr (L l (HsOverLit x lit)) =
  (\e -> L l (HsOverLit x (lit { ol_witness = unLoc e })))
    <$> preprocessExpr (noLoc (ol_witness lit))
preprocessExpr (L l (HsLam x mg)) = do
  mg' <- preprocessEquations mg
  return (L l (HsLam x mg'))
preprocessExpr (L l (HsLamCase x mg)) = do
  mg' <- preprocessEquations mg
  return (L l (HsLamCase x mg'))
preprocessExpr e@(L _ (HsConLikeOut _ _)) =
  return e
preprocessExpr (L l (OpApp x e1 op e2)) = do
  e1' <- preprocessExpr e1
  op' <- preprocessExpr op
  e2' <- preprocessExpr e2
  return (L l (OpApp x e1' op' e2'))
preprocessExpr (L l (HsApp x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (L l (HsApp x e1' e2'))
preprocessExpr (L l (HsAppType x e ty)) = do
  e' <- preprocessExpr e
  return (L l (HsAppType x e' ty))
preprocessExpr (L l (NegApp x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessSynExpr e2
  return (L l (NegApp x e1' e2'))
preprocessExpr (L l (HsPar x e)) = do
  e' <- preprocessExpr e
  return (L l (HsPar x e'))
preprocessExpr (L l (SectionL x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (L l (SectionL x e1' e2'))
preprocessExpr (L l (SectionR x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (L l (SectionR x e1' e2'))
preprocessExpr (L l (ExplicitTuple x args b)) = do
  args' <- mapM preprocessTupleArg args
  return (L l (ExplicitTuple x args' b))
preprocessExpr e@(L l ExplicitSum {}) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr (L l (HsCase x sc br)) = do
  br' <- preprocessEquations br
  sc' <- preprocessExpr sc
  return (L l (HsCase x sc' br'))
preprocessExpr (L l (HsIf x e1 e2 e3)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  e3' <- preprocessExpr e3
  return (L l (HsIf x e1' e2' e3'))
preprocessExpr e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
preprocessExpr (L l (HsLet x bs e)) = do
  bs' <- preprocessLocalBinds bs
  e' <- preprocessExpr e
  return (L l (HsLet x bs' e'))
preprocessExpr (L l1 (HsDo x ctxt (L l2 stmts))) = do
  stmts' <- preprocessStmts stmts
  return (L l1 (HsDo x ctxt (L l2 stmts')))
preprocessExpr (L l (ExplicitList x Nothing es)) = do
  es' <- mapM preprocessExpr es
  return (L l (ExplicitList x Nothing es'))
preprocessExpr e@(L l (ExplicitList _ (Just _) _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr (L l (RecordCon x cn (HsRecFields flds dd))) = do
  flds' <- mapM preprocessField flds
  return (L l (RecordCon x cn (HsRecFields flds' dd)))
preprocessExpr (L l (RecordUpd x e flds)) = do
  e' <- preprocessExpr e
  flds' <- mapM preprocessField flds
  return (L l (RecordUpd x e' flds'))
preprocessExpr (L l (ExprWithTySig x e ty)) = do
  e' <- preprocessExpr e
  return (L l (ExprWithTySig x e' ty))
preprocessExpr (L l (ArithSeq x Nothing i)) = do
  x' <- unLoc <$> preprocessExpr (noLoc x)
  i' <- preprocessArithExpr i
  return (L l (ArithSeq x' Nothing i'))
preprocessExpr e@(L l (ArithSeq _ (Just _) _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr (L l (HsPragE x (HsPragSCC a b c) e)) = do
  e' <- preprocessExpr e
  return (L l (HsPragE x (HsPragSCC a b c) e'))
preprocessExpr e@(L l (HsBracket _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr e@(L l (HsSpliceE _ _)) =  do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr e@(L l (HsTcBracketOut _ _ _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr e@(L l (HsProc _ _ _)) =  do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Arrow notation is not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr (L l (HsStatic x e)) = do
  L l . HsStatic x <$> preprocessExpr e
preprocessExpr (L l (HsTick a tick e)) = do
  e' <- preprocessExpr e
  return (L l (HsTick a tick e'))
preprocessExpr (L l (HsBinTick a b c e)) = do
  e' <- preprocessExpr e
  return (L l (HsBinTick a b c e'))
preprocessExpr (L l (XExpr (WrapExpr (HsWrap w e)))) = do
  e' <- unLoc <$> preprocessExpr (noLoc e)
  return (L l (XExpr (WrapExpr (HsWrap w e'))))
preprocessExpr (L _ (HsUnboundVar _ _)) = undefined
preprocessExpr (L _ (HsRecFld _ _)) = undefined
preprocessExpr (L _ (HsOverLabel _ _ _)) = undefined
preprocessExpr (L _ (HsIPVar _ _)) = undefined
preprocessExpr (L _ (HsRnBracketOut _ _ _)) = undefined
preprocessExpr (L _ (XExpr (ExpansionExpr _))) = undefined

preprocessArithExpr :: ArithSeqInfo GhcTc -> TcM (ArithSeqInfo GhcTc)
preprocessArithExpr (From e1) = From <$> preprocessExpr e1
preprocessArithExpr (FromThen e1 e2) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (FromThen e1' e2')
preprocessArithExpr (FromTo e1 e2) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (FromTo e1' e2')
preprocessArithExpr (FromThenTo e1 e2 e3) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  e3' <- preprocessExpr e3
  return (FromThenTo e1' e2' e3')

preprocessStmts :: [ExprLStmt GhcTc] -> TcM [ExprLStmt GhcTc]
preprocessStmts [] = return []
preprocessStmts (s:ss) = do
  s'  <- preprocessStmt s
  ss' <- preprocessStmts ss
  return (s':ss')
  where
    preprocessStmt (L l (LastStmt x e a r)) = do
      e' <- preprocessExpr e
      r' <- preprocessSynExpr r
      return (L l (LastStmt x e' a r'))
    preprocessStmt (L l (BindStmt (XBindStmtTc b m ty f) p e)) = do
      e' <- preprocessExpr e
      b' <- preprocessSynExpr b
      f'  <- maybe (return Nothing) (fmap Just . preprocessSynExpr) f
      return (L l (BindStmt (XBindStmtTc b' m ty f') p e'))
    preprocessStmt (L l (ApplicativeStmt _ _ _)) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Applicative do-notation is not supported by the plugin")
      failIfErrsM
      return s
    preprocessStmt (L l (BodyStmt x e sq g)) = do
      e'  <- preprocessExpr e
      sq' <- preprocessSynExpr sq
      g'  <- preprocessSynExpr g
      return (L l (BodyStmt x e' sq' g'))
    preprocessStmt (L l (LetStmt x bs)) = do
      bs' <- preprocessLocalBinds bs
      return (L l (LetStmt x bs'))
    preprocessStmt (L l (ParStmt _ _ _ _)) =  do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      failIfErrsM
      return s
    preprocessStmt (L l (TransStmt _ _ _ _ _ _ _ _ _)) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      failIfErrsM
      return s
    preprocessStmt (L l (RecStmt _ _ _ _ _ _ _)) =  do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Recursive do-notation is not supported by the plugin")
      failIfErrsM
      return s

preprocessSynExpr :: SyntaxExprTc -> TcM (SyntaxExpr GhcTc)
preprocessSynExpr (SyntaxExprTc e ws w) = do
  e' <- unLoc <$> preprocessExpr (noLoc e)
  return (SyntaxExprTc e' ws w)
preprocessSynExpr NoSyntaxExprTc = return NoSyntaxExprTc

preprocessField :: Located (HsRecField' a (LHsExpr GhcTc))
                -> TcM (Located (HsRecField' a (LHsExpr GhcTc)))
preprocessField (L l (HsRecField v e p)) = do
  e' <- preprocessExpr e
  return (L l (HsRecField v e' p))

preprocessTupleArg :: LHsTupArg GhcTc -> TcM (LHsTupArg GhcTc)
preprocessTupleArg (L l (Present x e)) =
  L l . Present x <$> preprocessExpr e
preprocessTupleArg x = return x

preprocessLocalBinds :: LHsLocalBinds GhcTc -> TcM (LHsLocalBinds GhcTc)
preprocessLocalBinds (L l (HsValBinds x b)) = do
  b' <- preprocessValBinds b
  return (L l (HsValBinds x b'))
preprocessLocalBinds bs@(L l (HsIPBinds _ _)) =  do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return bs
preprocessLocalBinds b = return b

preprocessValBinds :: HsValBindsLR GhcTc GhcTc
                   -> TcM (HsValBindsLR GhcTc GhcTc)
preprocessValBinds bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
preprocessValBinds (XValBindsLR (NValBinds bs sigs)) = do
  bs' <- mapM preprocessNV bs
  return (XValBindsLR (NValBinds bs' sigs))
  where
    preprocessNV :: (RecFlag, LHsBinds GhcTc)
                 -> TcM (RecFlag, LHsBinds GhcTc)
    preprocessNV (rf, b) = do
      bs' <- liftBag (preprocessBinding True) b
      return (rf, bs')
