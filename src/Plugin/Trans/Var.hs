{-|
Module      : Plugin.Trans.Var
Description : Various helper to create variables
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains various functions to generate fresh variables and other
stuff to deal with variables.
-}
module Plugin.Trans.Var where

import Data.Syb

import GHC.Types.Name.Occurrence
import GHC.Plugins
import GHC.Tc.Types
import GHC.Core.TyCo.Rep

-- | Create a fresh type variable of kind 'Type'.
freshSimpleTVar :: TcM TyVar
freshSimpleTVar = do
  u <- getUniqueM
  let k = liftedTypeKind
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "a")) k

-- | Create a fresh type variable of the given kind.
freshTVar :: Kind -> TcM TyVar
freshTVar k = do
  u <- getUniqueM
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "a")) k

-- | Create a fresh type variable of kind 'Type -> Type'.
freshMonadTVar :: TcM TyVar
freshMonadTVar = do
  u <- getUniqueM
  let k = liftedTypeKind
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "m"))
    (mkFunTy VisArg Many k k)

-- | Create a fresh variable of the given type.
freshVar :: Scaled Type -> TcM Var
freshVar (Scaled m ty) = do
  u <- getUniqueM
  let name = mkSystemName u (mkVarOcc "f")
  return $ mkLocalVar VanillaId name m ty vanillaIdInfo

-- | Create a fresh dictionary variable of the given type.
freshDictId :: Type -> TcM Var
freshDictId ty = do
  u <- getUniqueM
  let name = mkSystemName u (mkVarOcc "d")
  return $ mkLocalVar (DFunId True) name Many ty vanillaIdInfo

-- | Count the number of occurrences of the variable in the given term.
countVarOcc :: Data a => Var -> a -> Int
countVarOcc v e = length (listify (\v' -> varUnique v' == u) e)
  where u = varUnique v

-- | Change the unique of the given name and add "ND" as a suffix.
liftName :: Name -> Unique -> Name
liftName n u =
  let occ = occName n
      occ' = mkOccName (occNameSpace occ) (occNameString occ ++ "ND")
  in tidyNameOcc (setNameUnique n u) occ'
