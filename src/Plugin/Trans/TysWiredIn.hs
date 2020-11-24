{-|
Module      : Plugin.Trans.TysWiredIn
Description : Module to load built-in type constructors
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the function to load the initial type constructor map that
connects lifted and unlifted versions of a type constructor.
The map is initialized with some of GHC's built-in types.
-}
module Plugin.Trans.TysWiredIn (loadDefaultTyConMap, builtInModule) where

import Data.IORef
import Data.Tuple

import GHC.Types.Name.Occurrence
import GHC.Plugins
import GHC.Unit.Finder
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env
import GHC.Iface.Env
import GHC.Builtin.Names

import Plugin.Trans.Type

-- | Load the mapping between lifted and unlifted
-- for all built-in type constructors.
loadDefaultTyConMap :: TcM (IORef (UniqFM TyCon TyCon,
                                   UniqFM TyCon TyCon,
                                   UniqSet TyCon,
                                   UniqSet TyCon))
loadDefaultTyConMap = do
  -- Get list of original names and load replacements from the BuiltIn module.
  loaded <- mapM load originalNamesToLoad
  -- Load any other names that are not in 'PrelNames'
  others <- loadAdditional
  -- Create initial TyConMap
  let allLoaded  = others ++ loaded
  let allSwap    = map swap allLoaded
  let (old, new) = unzip allLoaded
  liftIO (newIORef (listToUFM allLoaded,
                    listToUFM allSwap,
                    mkUniqSet old,
                    mkUniqSet new))

-- | Get the lifted and unlifted TyCons
-- for the given original and replacement name.
load :: (Name, String) -> TcM (TyCon, TyCon)
load (n, s) = do
  old <- tcLookupTyCon n
  new <- getTyCon builtInModule s
  return (old, new)

-- | Get the lifted and unlifted TyCons of type constructors that are
-- not in 'PrelNames' for some reason.
loadAdditional :: TcM [(TyCon, TyCon)]
loadAdditional = do
  -- AlternativeClassName in PrelNames is incorrect, so we look it up manually
  hscEnv <- getTopEnv
  Found _ bse <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Base") Nothing
  altA <- tcLookupTyCon =<< lookupOrig bse ( mkTcOcc "Alternative" )
  newA <- getTyCon builtInModule "AlternativeND"

  -- String is not in PrelNames, so we do the same.
  altS <- tcLookupTyCon =<< lookupOrig bse ( mkTcOcc "String" )
  newS <- getTyCon builtInModule "StringND"

  -- And again for ShowS.
  Found _ shw <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Show") Nothing
  altH <- tcLookupTyCon =<< lookupOrig shw ( mkTcOcc "ShowS" )
  newH <- getTyCon builtInModule "ShowSND"

  -- And again for Real.
  Found _ real <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Real") Nothing
  altR <- tcLookupTyCon =<< lookupOrig real ( mkTcOcc "Real" )
  newR <- getTyCon builtInModule "RealND"

  -- And again for Integral
  altI <- tcLookupTyCon =<< lookupOrig real ( mkTcOcc "Integral" )
  newI <- getTyCon builtInModule "IntegralND"
  return [(altH, newH), (altR, newR), (altI, newI), (altA, newA), (altS, newS)]

-- | A list of GHC's built-in type constructor names and the names of
-- their plugin replacement version.
originalNamesToLoad :: [(Name, String)]
originalNamesToLoad = names
  where
    names =
      [ (eqClassName          , "EqND")
      , (ordClassName         , "OrdND")
      , (showClassName        , "ShowND")
      , (numClassName         , "NumND")
      , (fractionalClassName  , "FractionalND")
      , (enumClassName        , "EnumND")
      , (boundedClassName     , "BoundedND")
      , (functorClassName     , "FunctorND")
      , (applicativeClassName , "ApplicativeND")
      , (monadClassName       , "MonadND")
      , (monadFailClassName   , "MonadFailND")
      , (isStringClassName    , "IsStringND")
      , (listTyConName        , "ListND")
      , (rationalTyConName    , "RationalND")
      , (ratioTyConName       , "RatioND")
      ] ++
      map tupleWithArity [2 .. maxTupleArity]

-- | Create the GHC and plugin names for a tuple of given arity.
tupleWithArity :: Int -> (Name, String)
tupleWithArity n = (tupleTyConName BoxedTuple n, "Tuple" ++ show n ++ "ND")

-- | Max tuple arity supported by the plugin.
-- If this is increased, the new tuples
-- have to be added to 'Plugin.CurryPlugin.BuiltIn'.
maxTupleArity :: Int
maxTupleArity = 2

-- | Name of the module that contains all built-in plugin definitions
builtInModule :: String
builtInModule = "Plugin.CurryPlugin.BuiltIn"
