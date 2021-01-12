{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE Strict #-}
module Example where

import Plugin.CurryPlugin.Prelude

test :: Bool
test = not (null xs)
  where
    xs :: [Int]
    xs = 1 : xs

test2 :: Int
test2 = foldr (?) failed [1..]
