{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module ImportHaskell where

import Plugin.CurryPlugin.Prelude
import ExportHaskell

-- Compilation of this module is expected to fail
-- due to import of a plain Haskell module (see ExportHaskell.hs).
