{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE DefaultSignatures              #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module DefaultSignaturesExport where

import Plugin.CurryPlugin.Prelude


class FromInt a where
  fromIntDefault :: Int -> a
  default fromIntDefault :: Integral a => Int -> a
  fromIntDefault x = fromInteger (toInteger x)

instance FromInt Int
