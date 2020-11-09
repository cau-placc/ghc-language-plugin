{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE FunctionalDependencies         #-}
{-# LANGUAGE FlexibleInstances              #-}
module Example2 where

import Plugin.CurryPlugin.Prelude

infixr 5 `cons`
class ListLike l e | l -> e where
  nil    :: l
  cons   :: e -> l -> l
  uncons :: l -> Maybe (e, l)

instance ListLike [a] a where
  nil  = []
  cons = (:)
  uncons []     = Nothing
  uncons (x:xs) = Just (x, xs)

permutations :: ListLike l e => l -> l
permutations l = case uncons l of
    Nothing      -> nil
    Just (x, xs) -> insert x (permutations xs)
  where insert e l' = case uncons l' of
          Nothing      -> e `cons` nil
          Just (x, xs) -> (e `cons` x `cons` xs) ? (x `cons` insert e xs)
