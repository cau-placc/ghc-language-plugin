{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module GeneralizedNewtypeDeriving where

import Plugin.CurryPlugin.Prelude

newtype ListWrap a = L [a]
  deriving (Eq, Show, Functor, Applicative, Monad)
