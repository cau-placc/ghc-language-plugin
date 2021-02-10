module Plugin.CurryPlugin (plugin) where

import GHC.Plugins

import Plugin.LanguagePlugin
import Plugin.Trans.Config

plugin :: Plugin
plugin = setConfigFlagsFor flags languagePlugin
  where
    flags = [ (fst monadModConfigStr, "Plugin.Effect.Monad")
            , (fst monadNameConfigStr, "Nondet")
            , (fst preludeModConfigStr, "Plugin.CurryPlugin.Prelude")
            , (fst builtInModConfigStr, "Plugin.CurryPlugin.BuiltIn") ]
