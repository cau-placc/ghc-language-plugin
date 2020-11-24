{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module ScopedTypeVariables where

import Plugin.CurryPlugin.Prelude

appendAndReverseSelf :: forall a. [a] -> [a]
appendAndReverseSelf xs = ys ++ ys
     where
       ys :: [a]
       ys = reverse xs
