{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE StandaloneDeriving             #-}
{-# LANGUAGE TypeSynonymInstances           #-}
{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE DeriveFunctor                  #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module InstanceExport where

import Plugin.CurryPlugin.Prelude

newtype Id a = Id a

data Phantom a = Phantom

type Number = Phantom Int

instance Num Number where

deriving instance Show (Phantom a)

deriving instance Show a => Show (Id a)

deriving instance Functor Id

deriving instance Functor Phantom

instance Applicative Id where
  pure = Id
  Id f <*> Id a = Id (f a)

instance Monad Id where
  Id x >>= f = f x
