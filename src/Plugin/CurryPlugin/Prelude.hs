{-# LANGUAGE NoImplicitPrelude              #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns    #-}
{-# LANGUAGE RankNTypes                     #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-|
Module      : Plugin.CurryPlugin.ForeignExport
Description : Prelude for the Curry-Plugin
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module is the replacement Prelude to be used with the Curry-Plugin.
Most of these definitions are from Haskell's default Prelude and not from me.
-}
module Plugin.CurryPlugin.Prelude
  (module Plugin.CurryPlugin.Prelude, module Plugin.CurryPlugin.ForeignExport)
  where

import Plugin.CurryPlugin.ForeignExport