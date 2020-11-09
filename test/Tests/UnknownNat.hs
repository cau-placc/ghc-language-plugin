{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
module Tests.UnknownNat where

import Plugin.CurryPlugin.Prelude

unknownNat :: Int
unknownNat = 1 ? (unknownNat + 1)
