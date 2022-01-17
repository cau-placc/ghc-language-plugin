module Plugin.CurryPlugin (plugin) where

import GHC.Plugins

import Plugin.LanguagePlugin
import Plugin.Trans.Config

plugin :: Plugin
plugin = setConfigFlagsFor flags languagePlugin
  where
    flags = [ (fst monadModConfigStr, "Plugin.CurryPlugin.Monad")
            , (fst monadNameConfigStr, "Nondet")
            , (fst funModConfigStr, "Plugin.Effect.Classes")
            , (fst funNameConfigStr, ":-->")
            , (fst preludeModConfigStr, "Plugin.CurryPlugin.Prelude")
            , (fst builtInModConfigStr, "Plugin.CurryPlugin.BuiltIn") ]
