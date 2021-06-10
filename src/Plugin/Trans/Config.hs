{-|
Module      : Plugin.Trans.Config
Description : Configuration of the plugin
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains our various functions to get the configuration
required to execute the correct lifting.
We look up a few options to get the module and names of key definitions.
-}
module Plugin.Trans.Config where

import GHC.Types.Name.Occurrence hiding (varName)
import GHC.Plugins hiding (substTy, extendTvSubst)
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Iface.Env

import Plugin.Trans.Util

lookupConfig :: (HasDynFlags m, MonadIO m) => (String, String) -> m String
lookupConfig (configStr, errStr) = do
  opts <- pluginModNameOpts <$> getDynFlags
  case lookup (mkModuleName configStr) opts of
    Just x  -> return x
    Nothing -> panicAny errStr ()

setConfigFlagsFor :: [(String, String)] -> Plugin -> Plugin
setConfigFlagsFor flgs p@(Plugin { driverPlugin = dflagsPl }) =
  p { driverPlugin = setFlags }
  where
    setFlags opts hscEnv =
      let dflags = hsc_dflags hscEnv
          currentPluginOpts = pluginModNameOpts dflags
          newOpts = currentPluginOpts ++ [(mkModuleName m, v) | (m, v) <- flgs]
          newHsc = hscEnv { hsc_dflags = dflags { pluginModNameOpts = newOpts }}
      in dflagsPl opts newHsc

monadModConfigStr :: (String, String)
monadModConfigStr =
  ( "Plugin.LanguagePlugin.MonadMod"
  , "Missing module configuration for effect monad" )

monadNameConfigStr :: (String, String)
monadNameConfigStr =
  ( "Plugin.LanguagePlugin.MonadName"
  , "Missing name configuration for effect monad" )

preludeModConfigStr :: (String, String)
preludeModConfigStr =
  ( "Plugin.LanguagePlugin.PreludeMod"
  , "Missing module configuration for Prelude" )

builtInModConfigStr :: (String, String)
builtInModConfigStr =
  ( "Plugin.LanguagePlugin.BuiltInMod"
  , "Missing module configuration for BuiltIns" )

queryBuiltinFunctionName :: String -> TcM RdrName
queryBuiltinFunctionName fname = do
  modName <- lookupConfig monadModConfigStr
  mdl <- findImportedOrPanic modName
  nm <- lookupOrig mdl (mkVarOcc fname)
  return (Exact nm)
