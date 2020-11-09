{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
module Typeclass where

import Plugin.CurryPlugin.Prelude

-- Typeclasses are also supported

class Not a where
  myNot :: a -> a

instance Not Bool where
  myNot True = False
  myNot False = True

instance Not Int where

idNot :: Not a => a -> a
idNot x = myNot (myNot x)

test :: Bool
test = idNot True

-- Even deriving is possible
newtype WrappedBool = Wrap Bool
  deriving Eq

data Id a = Id a

instance Functor Id where
  -- artificially introduce sharing to test if a Shareable constraint on
  -- Id a is ok
  fmap f x = let (Id a, _) = (x, x) in Id (f a)
