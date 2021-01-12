{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE Strict #-}
{-|
Module      : Plugin.Effect.THEval
Description : Definition of choice trees and search algorithms
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the definition of the choice tree data structure and
search strategies used to collect nondeterministic results into a list.
-}
module Plugin.Effect.Tree (Tree(..), dfs, bfs) where

import Control.Monad
import Control.Applicative
import GHC.Exts

-- | Nondeterministic can be represented as trees, where results are
-- annotated at the leaves and nodes correspond to choices.
data Tree a = Failed
            | Leaf a
            | Choice (Tree a) (Tree a)
  deriving (Show, Functor)

instance Applicative Tree where
  pure = Leaf
  Failed       <*> _ = Failed
  Leaf f       <*> t = fmap f t
  Choice tl tr <*> t = Choice (tl <*> t) (tr <*> t)

instance Alternative Tree where
  empty = Failed
  (<|>) = Choice

instance Monad Tree where
  Failed       >>= _ = Failed
  Leaf a       >>= f = f a
  Choice tl tr >>= f = Choice (tl >>= f) (tr >>= f)

instance MonadFail Tree where
  fail _ = Failed

instance MonadPlus Tree where
  mzero = Failed
  mplus = Choice

-- * Search algorithms

-- | Depth-first traversal of a choice tree to collect results into a list.
dfs :: Tree a -> [a]
dfs t = dfs' t []
  where
    dfs' (Leaf a)       = (a:)
    dfs' (Choice t1 t2) = dfs' t1 . dfs' t2
    dfs' Failed         = id


-- | Breadth-first traversal of a choice tree to collect results into a list.
bfs :: Tree a -> [a]
bfs t = bfs' [t]
  where
    bfs' (Leaf   a     :< q) = a : bfs' q
    bfs' (Choice t1 t2 :< q) = bfs' (t2 :< t1 :< q)
    bfs' (Failed       :< q) = bfs' q
    bfs' Nil                 = []

---------------------------------------
-- Queue Implementation
---------------------------------------

data Queue a = Q [a] [a]
  deriving (Show, Eq, Ord, Functor)

{-# COMPLETE (:<), Nil #-}

infixr 5 :<
pattern (:<) :: a -> Queue a -> Queue a
pattern x :< xs <- (uncons -> Just (x, xs)) where
  x :< xs = enqueue x xs

pattern Nil :: Queue a
pattern Nil <- (uncons -> Nothing) where
  Nil = emptyQueue

instance IsList (Queue a) where
  type Item (Queue a) = a
  fromList = flip Q []
  toList (Q xs ys) = xs ++ reverse ys

instance Semigroup (Queue a) where
  Q []  _   <> q         = q
  Q xs1 ys1 <> Q xs2 ys2 = Q xs1 (ys1 ++ reverse xs2 ++ ys2)

instance Monoid (Queue a) where
  mempty = emptyQueue

emptyQueue :: Queue a
emptyQueue = Q [] []

enqueue :: a -> Queue a -> Queue a
enqueue x (Q xs ys) = queue xs (x:ys)

uncons :: Queue a -> Maybe (a, Queue a)
uncons q = (,) <$> peek q <*> dequeue q

peek :: Queue a -> Maybe a
peek (Q (x:_) _) = Just x
peek _           = Nothing

dequeue :: Queue a -> Maybe (Queue a)
dequeue (Q (_:xs) ys) = Just (queue xs ys)
dequeue _             = Nothing

-- Invariant: If the first list is empty, then also the second list is empty.
queue :: [a] -> [a] -> Queue a
queue [] ys = Q (reverse ys) []
queue xs ys = Q xs ys
