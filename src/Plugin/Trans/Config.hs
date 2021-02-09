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
import GHC.Unit.Finder
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Iface.Env

import Plugin.Trans.Util

lookupConfig :: (String, String) -> TcM String
lookupConfig (configStr, errStr) = do
  opts <- pluginModNameOpts <$> getDynFlags
  case lookup (mkModuleName configStr) opts of
    Just x  -> return x
    Nothing -> panicAny errStr ()

monadModConfigStr :: (String, String)
monadModConfigStr =
  ( "Plugin.LanguagePlugin.MonadMod"
  , "Missing module configuration for effect monad" )

monadNameConfigStr :: (String, String)
monadNameConfigStr =
  ( "Plugin.LanguagePlugin.MonadName"
  , "Missing name configuration for effect monad" )

queryBuiltinFunctionName :: String -> TcM RdrName
queryBuiltinFunctionName fname = do
  modName <- lookupConfig monadModConfigStr
  hscEnv <- getTopEnv
  Found _ mdl <- liftIO $
    findImportedModule hscEnv (mkModuleName modName) Nothing
  nm <- lookupOrig mdl (mkVarOcc fname)
  return (Exact nm)
