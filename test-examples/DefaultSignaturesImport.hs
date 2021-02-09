{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE DefaultSignatures              #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module DefaultSignaturesImport where

import Plugin.CurryPlugin.Prelude

import DefaultSignaturesExport

instance FromInt Integer

test1 :: Int
test1 = fromIntDefault 0

test2 :: Integer
test2 = fromIntDefault 0
