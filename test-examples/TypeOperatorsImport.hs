{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE TypeOperators                  #-}
module TypeOperatorsImport where

import Plugin.CurryPlugin.Prelude
import TypeOperatorsExport (type (:+:)(..))

mapBoth :: (a -> c) -> (b -> d) -> a :+: b -> c :+: d
mapBoth f g (a :+: b) = f a :+: g b 
