{-|
Module      : Plugin.Trans.Var
Description : Various helper to create variables
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains various functions to generate fresh variables and other
stuff to deal with variables.
-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Plugin.Trans.Var where

import Data.Data     (Data, Typeable, gmapQ)
import Data.Typeable (cast)

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

-- | Create a fresh type variable of kind 'Type -> Type'.
freshMonadTVar :: TcM TyVar
freshMonadTVar = do
  u <- getUniqueM
  let k = liftedTypeKind
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "a"))
    (mkFunTy VisArg Many k k)

-- | Create a fresh variable of the given type.
freshVar :: Type -> TcM Var
freshVar ty = do
  u <- getUniqueM
  let name = mkSystemName u (mkVarOcc "f")
  return $ mkLocalVar VanillaId name Many ty vanillaIdInfo

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

type GenericQ r = forall a. Data a => a -> r

-- | Get a list of all entities that meet a predicate
listify :: Typeable r => (r -> Bool) -> GenericQ [r]
listify p = everything (++) ([] `mkQ` (\x -> if p x then [x] else []))

everything :: forall r. (r -> r -> r) -> GenericQ r -> GenericQ r
everything k f = go
  where
    go :: GenericQ r
    go x = foldl k (f x) (gmapQ go x)

mkQ :: ( Typeable a
       , Typeable b
       )
    => r
    -> (b -> r)
    -> a
    -> r
(r `mkQ` br) a = case cast a of
                        Just b  -> br b
                        Nothing -> r
