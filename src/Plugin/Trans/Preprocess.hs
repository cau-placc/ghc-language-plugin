{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-} -- TODO
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
import GHC.Parser.Annotation

import Plugin.Trans.Util
import Plugin.Trans.Type
import Plugin.Trans.ConstraintSolver
import Plugin.Trans.PatternMatching

-- | Preprocess a binding before lifting, to get rid of nested pattern matching.
-- Also removes some explicit type applications and fuses HsWrapper.
preprocessBinding :: TyConMap -> Bool -> HsBindLR GhcTc GhcTc
                  -> TcM (HsBindLR GhcTc GhcTc)
preprocessBinding tcs lcl (AbsBinds a b c d e f g)
  -- Record selectors should stay like they are for now.
  | not (any (isRecordSelector . abe_poly) d) = do
  -- Rreprocess each binding seperate.
  bs <- liftBag (preprocessBinding tcs lcl) f
  return (AbsBinds a b c d e bs g)
preprocessBinding tcs lcl (FunBind a (L b name) eqs ticks) = do
  -- Compile pattern matching first, but only use matchExpr
  -- if this is a top-level binding to avoid doing this multiple times.
  Left matchedGr <- compileMatchGroup eqs
  matched <- (if lcl then return else everywhereM (mkM matchExpr)) matchedGr
  -- Preprocess the inner part of the declaration afterwards.
  eqs' <- preprocessEquations tcs matched
  return (FunBind a (L b name) eqs' ticks)
preprocessBinding _ _ a = return a

preprocessEquations :: TyConMap -> MatchGroup GhcTc (LHsExpr GhcTc)
                    -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
preprocessEquations tcs (MG a (L b alts) c) = do
  alts' <- mapM (preprocessAlt tcs) alts
  return (MG a (L b alts') c)

preprocessAlt :: TyConMap -> LMatch GhcTc (LHsExpr GhcTc)
              -> TcM (LMatch GhcTc (LHsExpr GhcTc))
preprocessAlt tcs (L a (Match b c d rhs)) = do
  rhs' <- preprocessRhs tcs rhs
  return (L a (Match b c d rhs'))

preprocessRhs :: TyConMap -> GRHSs GhcTc (LHsExpr GhcTc)
              -> TcM (GRHSs GhcTc (LHsExpr GhcTc))
preprocessRhs tcs (GRHSs a grhs b) = do
  grhs' <- mapM (preprocessGRhs tcs) grhs
  return (GRHSs a grhs' b)

preprocessGRhs :: TyConMap -> LGRHS GhcTc (LHsExpr GhcTc)
               -> TcM (LGRHS GhcTc (LHsExpr GhcTc))
preprocessGRhs tcs (L a (GRHS b c body)) = do
  body' <- preprocessExpr tcs body
  return (L a (GRHS b c body'))

-- preprocessExpr traverses the AST to reach all local function definitions
-- and removes some ExplicitTypeApplications.
-- Some HsWrapper might be split into two halves on each side of an
-- explicit type applications. We have to fuse those wrappers.
preprocessExpr :: TyConMap -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
preprocessExpr tcs (L l1 (HsVar x (L l2 v))) = do
  mtc <- getMonadTycon
  stc <- getShareClassTycon
  v' <- setVarType v . fst <$> liftIO (removeNondet tcs mtc stc (varType v))
  let e = (L l1 (HsVar x (L l2 v')))
  return e
preprocessExpr _ e@(L _ HsLit{}) =
  return e
preprocessExpr tcs (L l (HsOverLit x lit)) =
  (\e -> L l (HsOverLit x (lit { ol_witness = unLoc e })))
    <$> preprocessExpr tcs (noLocA (ol_witness lit))
preprocessExpr tcs (L l (HsLam x mg)) = do
  mg' <- preprocessEquations tcs mg
  return (L l (HsLam x mg'))
preprocessExpr tcs (L l (HsLamCase x mg)) = do
  mg' <- preprocessEquations tcs mg
  return (L l (HsLamCase x mg'))
preprocessExpr _ e@(L _ (HsConLikeOut _ _)) =
  return e
preprocessExpr tcs (L l (OpApp x e1 op e2)) = do
  e1' <- preprocessExpr tcs e1
  op' <- preprocessExpr tcs op
  e2' <- preprocessExpr tcs e2
  return (L l (OpApp x e1' op' e2'))
preprocessExpr tcs (L l (HsApp x e1 e2)) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  return (L l (HsApp x e1' e2'))
preprocessExpr tcs (L l (HsAppType ty e _)) = do
  e' <- unLoc <$> preprocessExpr tcs e
  case e' of
    (XExpr (WrapExpr (HsWrap w' e''))) ->
         return (L l (XExpr (WrapExpr (HsWrap (WpTyApp ty <.> w') e''))))
    _ -> return (L l (XExpr (WrapExpr (HsWrap (WpTyApp ty) e'))))
preprocessExpr tcs (L l (NegApp x e1 e2)) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessSynExpr tcs e2
  return (L l (NegApp x e1' e2'))
preprocessExpr tcs (L l (HsPar x e)) = do
  e' <- preprocessExpr tcs e
  return (L l (HsPar x e'))
preprocessExpr tcs (L l (SectionL x e1 e2)) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  return (L l (SectionL x e1' e2'))
preprocessExpr tcs (L l (SectionR x e1 e2)) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  return (L l (SectionR x e1' e2'))
preprocessExpr tcs (L l (ExplicitTuple x args b)) = do
  args' <- mapM (preprocessTupleArg tcs) args
  return (L l (ExplicitTuple x args' b))
preprocessExpr _ e@(L _ ExplicitSum {}) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr tcs (L l (HsCase x sc br)) = do
  br' <- preprocessEquations tcs br
  sc' <- preprocessExpr tcs sc
  return (L l (HsCase x sc' br'))
preprocessExpr tcs (L l (HsIf x e1 e2 e3)) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  e3' <- preprocessExpr tcs e3
  return (L l (HsIf x e1' e2' e3'))
preprocessExpr _ e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
preprocessExpr tcs (L l (HsLet x bs e)) = do
  bs' <- preprocessLocalBinds tcs (noLoc bs)
  e' <- preprocessExpr tcs e
  return (L l (HsLet x (unLoc bs') e'))
preprocessExpr tcs (L l1 (HsDo x ctxt (L l2 stmts))) = do
  stmts' <- preprocessStmts tcs stmts
  return (L l1 (HsDo x ctxt (L l2 stmts')))
preprocessExpr tcs (L l (ExplicitList ty es)) = do
  es' <- mapM (preprocessExpr tcs) es
  return (L l (ExplicitList ty es'))
preprocessExpr tcs (L l (RecordCon x cn (HsRecFields flds dd))) = do
  flds' <- mapM (preprocessField tcs) flds
  return (L l (RecordCon x cn (HsRecFields flds' dd)))
preprocessExpr tcs (L l (RecordUpd x e flds)) = do
  e' <- preprocessExpr tcs e
  flds' <- either (fmap Left . mapM (preprocessField tcs))
                  (fmap Right . mapM (preprocessField tcs)) flds
  return (L l (RecordUpd x e' flds'))
preprocessExpr tcs (L l (ExprWithTySig x e ty)) = do
  e' <- preprocessExpr tcs e
  return (L l (ExprWithTySig x e' ty))
preprocessExpr tcs (L l (ArithSeq x Nothing i)) = do
  x' <- unLoc <$> preprocessExpr tcs (noLocA x)
  i' <- preprocessArithExpr tcs i
  return (L l (ArithSeq x' Nothing i'))
preprocessExpr _ e@(L _ (ArithSeq _ (Just _) _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr tcs (L l (HsPragE x (HsPragSCC a b c) e)) = do
  e' <- preprocessExpr tcs e
  return (L l (HsPragE x (HsPragSCC a b c) e'))
preprocessExpr _ e@(L _ (HsBracket _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr _ e@(L _ (HsSpliceE _ _)) =  do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr _ e@(L _ (HsTcBracketOut _ _ _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr _ e@(L _ (HsProc _ _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Arrow notation is not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr tcs (L l (HsStatic x e)) = do
  L l . HsStatic x <$> preprocessExpr tcs e
preprocessExpr tcs (L l (HsTick a tick e)) = do
  e' <- preprocessExpr tcs e
  return (L l (HsTick a tick e'))
preprocessExpr tcs (L l (HsBinTick a b c e)) = do
  e' <- preprocessExpr tcs e
  return (L l (HsBinTick a b c e'))
preprocessExpr tcs (L l (XExpr (WrapExpr (HsWrap w e)))) = do
  e' <- unLoc <$> preprocessExpr tcs (noLocA e)
  case e' of
    (XExpr (WrapExpr (HsWrap w' e''))) ->
         return (L l (XExpr (WrapExpr (HsWrap (w <.> w') e''))))
    _ -> return (L l (XExpr (WrapExpr (HsWrap w e'))))
preprocessExpr _ (L _ (HsUnboundVar _ _)) = undefined
preprocessExpr _ (L _ (HsRecFld _ _)) = undefined
preprocessExpr _ (L _ (HsOverLabel _ _)) = undefined
preprocessExpr _ e@(L _ (HsIPVar _ _)) = do
  reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return e
preprocessExpr _ (L _ (HsRnBracketOut _ _ _)) = undefined
preprocessExpr _ (L _ (HsGetField _ _ _)) = undefined -- TODO
preprocessExpr _ (L _ (HsProjection _ _)) = undefined -- TODO
preprocessExpr _ (L _ (XExpr (ExpansionExpr _))) = undefined

preprocessArithExpr :: TyConMap -> ArithSeqInfo GhcTc
                    -> TcM (ArithSeqInfo GhcTc)
preprocessArithExpr tcs (From e1) = From <$> preprocessExpr tcs e1
preprocessArithExpr tcs (FromThen e1 e2) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  return (FromThen e1' e2')
preprocessArithExpr tcs (FromTo e1 e2) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  return (FromTo e1' e2')
preprocessArithExpr tcs (FromThenTo e1 e2 e3) = do
  e1' <- preprocessExpr tcs e1
  e2' <- preprocessExpr tcs e2
  e3' <- preprocessExpr tcs e3
  return (FromThenTo e1' e2' e3')

preprocessStmts :: TyConMap -> [ExprLStmt GhcTc] -> TcM [ExprLStmt GhcTc]
preprocessStmts _ [] = return []
preprocessStmts tcs (s:ss) = do
  s'  <- preprocessStmt s
  ss' <- preprocessStmts tcs ss
  return (s':ss')
  where
    preprocessStmt (L l (LastStmt x e a r)) = do
      e' <- preprocessExpr tcs e
      r' <- preprocessSynExpr tcs r
      return (L l (LastStmt x e' a r'))
    preprocessStmt (L l (BindStmt (XBindStmtTc b m ty f) p e)) = do
      e' <- preprocessExpr tcs e
      b' <- preprocessSynExpr tcs b
      f'  <- maybe (return Nothing) (fmap Just . preprocessSynExpr tcs) f
      return (L l (BindStmt (XBindStmtTc b' m ty f') p e'))
    preprocessStmt (L _ (ApplicativeStmt _ _ _)) = do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Applicative do-notation is not supported by the plugin")
      failIfErrsM
      return s
    preprocessStmt (L l (BodyStmt x e sq g)) = do
      e'  <- preprocessExpr tcs e
      sq' <- preprocessSynExpr tcs sq
      g'  <- preprocessSynExpr tcs g
      return (L l (BodyStmt x e' sq' g'))
    preprocessStmt (L l (LetStmt x bs)) = do
      bs' <- preprocessLocalBinds tcs (noLoc bs)
      return (L l (LetStmt x (unLoc bs')))
    preprocessStmt (L _ (ParStmt _ _ _ _)) =  do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      failIfErrsM
      return s
    preprocessStmt (L _ (TransStmt _ _ _ _ _ _ _ _ _)) = do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      failIfErrsM
      return s
    preprocessStmt (L _ (RecStmt _ _ _ _ _ _ _)) =  do
      reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Recursive do-notation is not supported by the plugin")
      failIfErrsM
      return s

preprocessSynExpr :: TyConMap -> SyntaxExprTc -> TcM (SyntaxExpr GhcTc)
preprocessSynExpr tcs (SyntaxExprTc e ws w) = do
  e' <- unLoc <$> preprocessExpr tcs (noLocA e)
  return (SyntaxExprTc e' ws w)
preprocessSynExpr _ NoSyntaxExprTc = return NoSyntaxExprTc

preprocessField :: TyConMap -> GenLocated l (HsRecField' a (LHsExpr GhcTc))
                -> TcM (GenLocated l (HsRecField' a (LHsExpr GhcTc)))
preprocessField tcs (L l (HsRecField x v e p)) = do
  e' <- preprocessExpr tcs e
  return (L l (HsRecField x v e' p))

preprocessTupleArg :: TyConMap -> HsTupArg GhcTc -> TcM (HsTupArg GhcTc)
preprocessTupleArg tcs (Present x e) =
  Present x <$> preprocessExpr tcs e
preprocessTupleArg _ x = return x

preprocessLocalBinds :: TyConMap -> GenLocated l (HsLocalBinds GhcTc)
                     -> TcM (GenLocated l (HsLocalBinds GhcTc))
preprocessLocalBinds tcs (L l (HsValBinds x b)) = do
  b' <- preprocessValBinds tcs b
  return (L l (HsValBinds x b'))
preprocessLocalBinds _ bs@(L _ (HsIPBinds _ _)) =  do
  reportError (mkMsgEnvelope noSrcSpan neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return bs
preprocessLocalBinds _ b = return b

preprocessValBinds :: TyConMap -> HsValBindsLR GhcTc GhcTc
                   -> TcM (HsValBindsLR GhcTc GhcTc)
preprocessValBinds _ bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
preprocessValBinds tcs (XValBindsLR (NValBinds bs sigs)) = do
  bs' <- mapM preprocessNV bs
  return (XValBindsLR (NValBinds bs' sigs))
  where
    preprocessNV :: (RecFlag, LHsBinds GhcTc)
                 -> TcM (RecFlag, LHsBinds GhcTc)
    preprocessNV (rf, b) = do
      bs' <- liftBag (preprocessBinding tcs True) b
      return (rf, bs')
