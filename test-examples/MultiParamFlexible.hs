{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
module MultiParamFlexible where

import Plugin.CurryPlugin.Prelude

class ListLike e l | l -> e where
  cons :: e -> l -> l
  uncons :: l -> Maybe (e, l)
  nil :: l

instance ListLike a [a] where
  cons = (:)
  uncons [] = Nothing
  uncons (x:xs) = Just (x, xs)
  nil = []

nilList :: ListLike e [e] => [e]
nilList = nil
