{-|
Module      : Plugin.Trans.FunWiredIn
Description : Functions to look up the replacement of wired-in functions
Copyright   : (c) Kai-Oliver Prott (2020 - 2023)
Maintainer  : kai.prott@hotmail.de

This module provides a look up for wired-in functions.
There are two reasons to replace a function:
  1. It is used in a derived instance.
     Derived instances always use the functions from the default Prelude.
  2. It is a default implementation of a built-in type class that requires
     Sharing. Adding a Shareable constraints to built-in class
     functions is not supported, so we replace any used default implementation
     with something different during lifting.
-}
module Plugin.Trans.FunWiredIn
  (lookupWiredInFunc)
  where

import Data.List

import GHC.Types.Name.Occurrence hiding (varName)
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Utils.Env
import GHC.Iface.Env
import GHC.Builtin.Names

import Plugin.Trans.Config
import Plugin.Trans.Util

-- | look up the replacement for a wired-in function or return the original
-- if no replacement is known or required.
lookupWiredInFunc :: Var -> TcM (Maybe Var)
lookupWiredInFunc v = do
  wired <- mapM lookupRdrBase wiredIn
  builtInModule <- lookupConfig builtInModConfigStr
  case find (== varName v) wired of
    Nothing -> return Nothing
    Just n -> Just <$> do
      mdl <- findImportedOrPanic builtInModule
      tcLookupId =<< lookupOrig mdl (occName n)

-- | Look up the Name for a given RdrName
-- where the original name is already known.
lookupRdrBase :: RdrName -> TcM Name
lookupRdrBase n = case isOrig_maybe n of
  Nothing     -> panicAnyUnsafe "Wired-In name was not original" n
  Just (m, o) -> lookupOrig m o

-- A list of all wired-in functions. Their replacement always has the same name
-- and is defined in 'Plugin.CurryPlugin.BuiltIn'.
wiredIn :: [RdrName]
wiredIn =
  [ mkOrig gHC_CLASSES (mkVarOcc "and")
  , mkOrig gHC_CLASSES (mkVarOcc "not")
  , mkOrig gHC_PRIM    (mkVarOcc "coerce")
  , mkOrig mONAD       (mkVarOcc "guard")
  , mkOrig gHC_BASE    (mkVarOcc "map")
  , mkOrig gHC_BASE    (mkVarOcc "eqString")
  , mkOrig gHC_SHOW    (mkVarOcc "showString")
  , mkOrig gHC_SHOW    (mkVarOcc "showCommaSpace")
  , mkOrig gHC_SHOW    (mkVarOcc "showSpace")
  , mkOrig gHC_SHOW    (mkVarOcc "showParen")
  , mkOrig gHC_BASE    (mkVarOcc ".")
  , mkOrig gHC_PRIM    (mkVarOcc "seq")
  , mkOrig gHC_PRIM    (mkVarOcc "<#")
  , mkOrig gHC_PRIM    (mkVarOcc "==#")
  , mkOrig gHC_PRIM    (mkVarOcc "leftSection")
  , mkOrig gHC_PRIM    (mkVarOcc "rightSection")
  ]
