{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
module Import where

import Plugin.CurryPlugin.Prelude
-- We can import other modules and use their definitions.
import Export

test :: Result Bool Int
test = e (Err 1)

e :: Result b a -> Result a b
e = result Ok Err
