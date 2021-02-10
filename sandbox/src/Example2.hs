{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns    #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE FunctionalDependencies         #-}
{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE ViewPatterns                   #-}
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
permutations (uncons -> Nothing     ) = nil
permutations (uncons -> Just (x, xs)) = insert x (permutations xs)

insert :: ListLike l e => e -> l -> l
insert e (uncons -> Nothing     ) = e `cons` nil
insert e (uncons -> Just (x, xs)) = (e `cons` x `cons` xs) ?
                                    (x `cons` insert e xs)
