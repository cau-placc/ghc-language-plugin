{-# LANGUAGE NoImplicitPrelude   #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module Sections where

import Plugin.CurryPlugin.Prelude

test :: Int -> String
test = (===True)

test2 :: Bool -> String
test2 = (0===)

(===) :: Int -> Bool -> String
_ === _ = ""
