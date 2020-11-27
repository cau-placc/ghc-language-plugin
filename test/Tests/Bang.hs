{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE BangPatterns                   #-}
module Tests.Bang (testBang, testNoBang) where

import Plugin.CurryPlugin.Prelude

test :: a -> ()
test !_ = ()

testNo :: a -> ()
testNo a = ()

testBang :: ()
testBang = test (failed :: ())

testNoBang :: ()
testNoBang = testNo (failed :: ())
