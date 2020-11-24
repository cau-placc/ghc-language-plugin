{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE TypeOperators                  #-}
module TypeOperatorsExport (type (:+:)(..)) where

import Plugin.CurryPlugin.Prelude

data a :+: b = a :+: b
