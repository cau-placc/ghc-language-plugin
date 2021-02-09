{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE LambdaCase                     #-}
module PatternMatching where

import Plugin.CurryPlugin.Prelude

-- Pattern matching is also supported by the plugin.

myNot :: Bool -> Bool
myNot True  = False
myNot False = True

true :: Bool
true = True

mappend :: Maybe a -> Maybe a -> Maybe a
mappend Nothing    y = y
mappend x@(Just _) _ = x

mappendFlipped :: Maybe a -> Maybe a -> Maybe a
mappendFlipped x = \case
  Nothing    -> x
  y@(Just _) -> y

maybeFold :: b -> (a -> b) -> Maybe a -> b
maybeFold b f m = case m of
  Just a  -> f a
  Nothing -> b

test :: Bool
test = maybeFold true myNot (Just False)
