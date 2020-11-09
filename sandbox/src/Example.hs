{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin -O2 #-}
{-# LANGUAGE NoImplicitPrelude                  #-}
{-# LANGUAGE BangPatterns #-}
module Example where

import Plugin.CurryPlugin.Prelude

data X = X {-# UNPACK #-} !Int

test :: X -> X -> X
test (X n) (X m) = X (n + m)
