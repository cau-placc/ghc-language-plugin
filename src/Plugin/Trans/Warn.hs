{-# LANGUAGE OverloadedStrings #-}
module Plugin.Trans.Warn (addNondetWarn) where

import Data.List

import GHC.Plugins
import GHC.Types.Error

addNondetWarn :: WarnMsg -> WarnMsg
addNondetWarn e = case errMsgDoc e of
  ErrDoc [m] ctxt suppl
    | "Pattern match(es) are non-exhaustive" `isPrefixOf`
      renderWithContext defaultSDocContext m
    -> e { errMsgDoc = ErrDoc [m] ctxt (txt : suppl) }
    where
      txt = "A failed match is transformed to a" $+$ "non-deterministic failure"
  _  -> e
