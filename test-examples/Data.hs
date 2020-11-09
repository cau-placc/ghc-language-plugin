{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
module Data where

import Plugin.CurryPlugin.Prelude

-- Datatypes can be translated ...
data MyMaybe a = MyJust a
               | MyNothing

-- ... and newtypes as well.
newtype Wrap a = Proxy a

data Test a 
