{-# LANGUAGE DeriveFunctor #-}
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
bfs = dfs
