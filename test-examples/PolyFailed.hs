{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module PolyFailed where

import Plugin.CurryPlugin.Prelude

test :: String -> a
test _ = failed
