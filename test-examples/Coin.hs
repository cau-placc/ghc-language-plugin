{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
module Coin where

import Plugin.CurryPlugin.Prelude

-- Nondeterministic choice between True and False.
coin :: Bool
coin = True ? False
