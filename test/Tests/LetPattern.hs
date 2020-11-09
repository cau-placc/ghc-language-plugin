{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
module Tests.LetPattern where

import Plugin.CurryPlugin.Prelude

letPattern :: Int
letPattern = let (Nothing, x) = (failed, 1) in x
