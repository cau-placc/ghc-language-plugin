{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilies              #-}
{-|
Module      : Plugin.Effect.CurryEffect
Description : Implementation of nondeterminism with sharing
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains defintions for a nondeterminism monad with support for
explicit sharing of computations.
It is adapted from a library explicit-sharing and a paper
by Sebastian Fischer et al.
"Purely functional lazy nondeterministic programming",
with slight modifications in the definition of the 'Lazy' datatype
and the 'collect' function.
We also had to adapt the implementation to the new GHC library, by mainly
adding a few missing instances.
-}
module Plugin.Effect.CurryEffect where

import qualified Data.IntMap         as M
import           Control.Monad
import           Control.Monad.State ( MonadState(..), gets, modify )
import           Control.Applicative
import           Unsafe.Coerce

import Plugin.Effect.Classes

-- | A Lazy implementation of a monad for nondeterminism
-- with support for explicit sharing.
newtype Lazy a = Lazy {
    fromLazy :: forall n . Nondet n => (a -> Store -> n) -> Store -> n
  } deriving Functor

-- | Collect all results into a given nondeterministic
-- and monadic data structure.
collect :: (Monad m, Nondet (m n)) => Lazy n -> (m n)
collect a = runLazy (fmap return a)

-- | Collect all results into a given nondeterministic data structure.
runLazy :: Nondet n => Lazy n -> n
runLazy m = fromLazy m (\a _ -> a) emptyStore

instance Applicative Lazy where
  {-# INLINE pure #-}
  pure = pureL
  (<*>) = ap

instance Alternative Lazy where
  {-# INLINE empty #-}
  empty = mzero
  {-# INLINE (<|>) #-}
  (<|>) = mplus

instance Monad Lazy where
  {-# INLINE (>>=) #-}
  (>>=) = andThen

{-# RULES
"pure/bind"   forall f x. andThen (pureL x) f = f x
  #-}

{-# INLINE[0] pureL #-}
-- | Inlineable implementation of 'pure' for 'Lazy'
pureL :: a -> Lazy a
pureL x = Lazy (\c -> c x)

{-# INLINE[0] andThen #-}
-- | Inlineable implementation of '(>>=)' for 'Lazy'
andThen :: Lazy a -> (a -> Lazy b) -> Lazy b
andThen a k = Lazy (\c s -> fromLazy a (\x -> fromLazy (k x) c) s)

instance MonadFail Lazy where
  fail _ = Lazy (\_ _ -> failure)

instance MonadPlus Lazy where
  mzero = Lazy (\_ _ -> failure)
  a `mplus` b = Lazy (\c s -> fromLazy a c s ? fromLazy b c s)

instance MonadState Store Lazy where
  get = Lazy (\c s -> c s s)
  put s = Lazy (\c _ -> c () s)

instance Sharing Lazy where
  type ShareConstraints Lazy a = Shareable Lazy a
  share a = memo (a >>= shareArgs share)
  shareTopLevel = const id

-- | A data type to label and store shared nondeterministic values
-- on an untyped heap.
data Store = Store
  { nextLabel :: !Int
  , heap :: !(M.IntMap Untyped)
  }

-- | An empty storage.
emptyStore :: Store
emptyStore = Store 0 M.empty

-- | Get a new fresh label.
freshLabel :: MonadState Store m => m Int
freshLabel = do
  s <- get
  put (s {nextLabel = nextLabel s + 1})
  return (nextLabel s)

-- | Look up the vaule for a given label in the store.
lookupValue :: MonadState Store m => Int -> m (Maybe a)
lookupValue k = gets (fmap typed . M.lookup k . heap)

-- | Store a given value for later.
storeValue :: MonadState Store m => Int -> a -> m ()
storeValue k v = modify (\s -> s { heap = M.insert k (Untyped v) (heap s) })

{-# INLINE memo #-}
-- | Memorize a nondeterministic value for explicit sharing.
memo :: Lazy a -> Lazy (Lazy a)
memo a =
  Lazy
    (\c1 (Store key heap1) ->
       c1
         (Lazy
            (\c2 s@(Store _ heap2) ->
               case M.lookup key heap2 of
                 Just x -> c2 (typed x) s
                 Nothing ->
                   fromLazy
                     a
                     (\x (Store other heap3) ->
                        c2 x (Store other (M.insert key (Untyped x) heap3)))
                     s))
         (Store (succ key) heap1))

-- | Wrap a typed value in an untyped container.
data Untyped = forall a. Untyped a

-- | Extract a typed value from an untyped container.
typed :: Untyped -> a
typed (Untyped x) = unsafeCoerce x
