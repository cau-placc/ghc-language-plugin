{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE StandaloneDeriving             #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module InstanceExport where

import Plugin.CurryPlugin.Prelude

newtype Id a = Id a

data Phantom a = Phantom

deriving instance Show (Phantom a)

deriving instance Show a => Show (Id a)

instance Functor Id where
  fmap f (Id a) = Id (f a)

instance Applicative Id where
  pure = Id
  Id f <*> Id a = Id (f a)

instance Monad Id where
  Id x >>= f = f x
