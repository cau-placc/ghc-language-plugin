{-|
Module      : Plugin.Trans.FunWiredIn
Description : Functions to look up the replacement of wired-in functions
Copyright   : (c) Kai-Oliver Prott (2020)
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
  (lookupWiredInFunc, lookupDefaultReplacement)
  where

import Data.List

import GHC.Types.Name.Occurrence hiding (varName)
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Utils.Env
import GHC.Iface.Env
import GHC.Builtin.Names
import GHC.Core.Class

import Plugin.Trans.Config
import Plugin.Trans.Util

-- | look up the replacement for the default implementation of a built-in
-- type class function.
lookupDefaultReplacement :: TyCon -> TyCon -> Name -> TcM Var
lookupDefaultReplacement tc tc' oldnm = do
    builtInModule <- lookupConfig builtInModConfigStr
    -- detect the old and new class first.
    case tyConClass_maybe tc of
      Nothing     -> panicAny "Expected a class, but recieved" tc
      Just oldCls ->
        case tyConClass_maybe tc' >>= find defLike . classOpItems of
          Nothing           -> panicAny "Expected a class, but recieved" tc'
          Just (_, Nothing) -> panicAny "Could not find default method for" tc'
          Just (_, Just (newnm, _)) ->
            case lookup (categorize (className oldCls) oldnm)
                    defaultReplacements of
              Nothing -> tcLookupId newnm
              -- Create the required replacement variable and get its type.
              Just nm -> do
                mdl <- findImportedOrPanic builtInModule
                tcLookupId =<< lookupOrig mdl nm
  where
    defLike (_ , Just (n', _)) = occName oldnm == occName n'
    defLike _                  = False

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

-- | Enumeration of all type class function classifications with respect to the
-- replacement of a default method.
data BuiltInDefaultCategory = OrdClassMax
                            | OrdClassMin
                            | IntegralClassDivMod
                            | OtherClassOrDefault
  deriving Eq

-- | Get the correct category for a given class and function name.
categorize :: Name -> Name -> BuiltInDefaultCategory
categorize cn dn
  | cn == ordClassName
    = case occNameString (occName dn) of
      s | "$dmmax"    `isPrefixOf` s -> OrdClassMax
        | "$dmmin"    `isPrefixOf` s -> OrdClassMin
        | otherwise                  -> OtherClassOrDefault
  | cn == integralClassName
    = case occNameString (occName dn) of
      s | "$dmdivMod" `isPrefixOf` s -> IntegralClassDivMod
        | otherwise                  -> OtherClassOrDefault
  | otherwise
    = OtherClassOrDefault

-- | A map to match a caegorized default method from a type class
-- with its replacement function name.
defaultReplacements :: [(BuiltInDefaultCategory, OccName)]
defaultReplacements =
  [ (OrdClassMax        , mkVarOcc "maxDefault")
  , (OrdClassMin        , mkVarOcc "minDefault")
  , (IntegralClassDivMod, mkVarOcc "divModDefault")
  ]

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
