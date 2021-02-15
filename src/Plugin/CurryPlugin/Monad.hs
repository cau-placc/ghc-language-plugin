{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE DeriveLift                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DerivingStrategies         #-}
{-|
Module      : Plugin.CurryPlugin.Monad
Description : Convenience wrapper for the effect
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the actual monad used by the plugin and a few
convenicence functions.
The monad type is a wrapper over the
'Lazy' type from 'Plugin.Effect.CurryEffect'.
-}
module Plugin.CurryPlugin.Monad
  ( Nondet(..), type (-->), (?), failed, share
  , SearchMode(..)
  , Normalform(..), modeOp, allValues, allValuesNF
  , NondetTag(..)
  , liftNondet1, liftNondet2
  , apply1, apply2, apply2Unlifted, apply3
  , bind, rtrn, fmp, shre, shreTopLevel, seqValue)
  where

import Language.Haskell.TH.Syntax
import Control.Monad

import Plugin.Effect.Classes
import Plugin.CurryPlugin.Tree
import Plugin.Effect.Annotation
import Plugin.Effect.Transformers

-- | The actual monad for nondeterminism used by the plugin.
newtype Nondet a = Nondet { unNondet :: LazyT Tree a }
  deriving newtype  (Functor, Applicative, Monad)
  deriving anyclass (SharingTop)

{-# INLINE[0] bind #-}
bind :: Nondet a -> (a -> Nondet b) -> Nondet b
bind = (>>=)

{-# INLINE[0] rtrn #-}
rtrn :: a -> Nondet a
rtrn = pure

{-# INLINE[0] fmp #-}
fmp :: (a -> b) -> Nondet a -> Nondet b
fmp = fmap

{-# INLINE[0] shre #-}
shre :: Shareable Nondet a => Nondet a -> Nondet (Nondet a)
shre a = mkShareNeedImpl @Tree (shareArgs shre) a

instance Sharing Nondet where
  type ShareConstraints Nondet a = Shareable Nondet a
  share = shre

{-# INLINE[0] shreTopLevel #-}
shreTopLevel :: (Int, String) -> Nondet a -> Nondet a
shreTopLevel = shareTopLevel

{-# INLINE seqValue #-}
seqValue :: Nondet a -> Nondet b -> Nondet b
seqValue a b = a >>= \a' -> a' `seq` b

{-# RULES
"bind/rtrn"    forall f x. bind (rtrn x) f = f x
"shreTopLevel" forall x i. shreTopLevel i x = x
  #-}
  -- "bind/rtrn'let"   forall e x. let b = e in rtrn x = rtrn (let b = e in x)

-- | Nondeterministic failure
failed :: Shareable Nondet a => Nondet a
failed = Nondet mzero

infixr 0 ?
{-# INLINE (?) #-}
-- | Nondeterministic choice
(?) :: Shareable Nondet a => Nondet (a --> a --> a)
(?) = return $
  \(Nondet t1) -> return $
  \(Nondet t2) -> Nondet (t1 `mplus` t2)

-- | Enumeration of available search modes.
data SearchMode = DFS -- ^ depth-first search
                | BFS -- ^ breadth-first search
  deriving Lift

-- | Function to map the search type to the function implementing it.
modeOp :: SearchMode -> Tree a -> [a]
modeOp DFS = dfs
modeOp BFS = bfs

-- | Collect the results of a nondeterministic computation
-- as their normal form in a tree.
allValuesNF :: Normalform Nondet a b
            => Nondet a -> Tree b
allValuesNF = allValues . nf

-- | Collect the results of a nondeterministic computation in a tree.
allValues :: Nondet a -> Tree a
allValues = runLazyT . unNondet

infixr 0 -->
type a --> b = (Nondet a -> Nondet b)

-- | Lift a unary function with the lifting scheme of the plugin.
liftNondet1 :: (a -> b) -> Nondet (a --> b)
liftNondet1 f = return (\a -> a >>= \a' -> return (f a'))

-- | Lift a 2-ary function with the lifting scheme of the plugin.
liftNondet2 :: (a -> b -> c) -> Nondet (a --> b --> c)
liftNondet2 f = return (\a  -> return (\b  ->
                a >>=   \a' -> b >>=   \b' -> return (f a' b')))

-- | Apply a lifted unary function to its lifted argument.
apply1 :: Nondet (a --> b) -> Nondet a -> Nondet b
apply1 f a = f >>= ($ a)

-- | Apply a lifted 2-ary function to its lifted arguments.
apply2 :: Nondet (a --> b --> c) -> Nondet a -> Nondet b -> Nondet c
apply2 f a b = apply1 f a >>= ($ b)

-- | Apply a lifted 2-ary function to its arguments, where just the
-- first argument has to be lifted.
apply2Unlifted :: Nondet (a --> b --> c)
               -> Nondet a -> b -> Nondet c
apply2Unlifted f a b = apply1 f a >>= ($ return b)

-- | Apply a lifted 3-ary function to its lifted arguments.
apply3 :: Nondet (a --> b --> c --> d)
       -> Nondet a -> Nondet b -> Nondet c -> Nondet d
apply3 f a b c = apply2 f a b >>= ($ c)
