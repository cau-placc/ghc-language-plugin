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
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# OPTIONS_GHC -Wno-orphans            #-}
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
  ( Lifted, Nondet(..), type (:-->)(..), type (-->), (?), failed, share
  , SearchMode(..)
  , Normalform(..), modeOp, allValues, allValuesNF
  , NondetTag(..)
  , liftNondet1, liftNondet2, liftNondet1NF, liftNondet2NF
  , app, apply2, apply2Unlifted, apply3
  , bind, rtrn, rtrnFunc, fmp, shre, shreTopLevel, seqValue
  , rtrnFuncUnsafePoly, appUnsafePoly )
  where

import Language.Haskell.TH.Syntax (Lift)
import Control.Applicative
import Control.Monad
import Unsafe.Coerce

import Plugin.Effect.Classes
import Plugin.CurryPlugin.Tree
import Plugin.Effect.Annotation
import Plugin.Effect.Transformers

-- | The actual monad for nondeterminism used by the plugin.
newtype Nondet a = Nondet { unNondet :: LazyT Nondet Tree a }
  deriving (Functor, Applicative, Monad, Alternative, MonadPlus, Sharing)
    via LazyT Nondet Tree
  deriving anyclass (SharingTop)

{-# INLINE[0] bind #-}
bind :: Nondet a -> (a -> Nondet b) -> Nondet b
bind = (>>=)

{-# INLINE[0] rtrn #-}
rtrn :: a -> Nondet a
rtrn = pure

{-# INLINE[0] rtrnFunc #-}
rtrnFunc :: (Nondet a -> Nondet b) -> Nondet (a --> b)
rtrnFunc = pure . Func

{-# INLINE[0] app #-}
app :: Nondet (a --> b) -> Nondet a -> Nondet b
app mf ma = mf >>= \(Func f) -> f ma

-- HACK:
-- RankNTypes are not really supported for various reasons,
-- but to test rewrite rules, we needed them to be supported at least
-- when the functions with RankN types are used and defined in the same module.
-- However, imagine we have a lambda with a (rank 2) type
-- (forall x. blah) -> blub.
-- Its lifted variant is something like
-- (forall x. blah') --> blub'
-- If we "unpack" the (-->) type constructor we get
-- m (forall x. blah') -> m blub'
-- This is bad, because the lifted type of the argument (forall x. blah)
-- is (forall x. m blah') and not m (forall x. blah').
-- To remedy this, we provide the following two functions using unsafeCoerce to
-- accomodate such a RankN type.
{-# INLINE[0] rtrnFuncUnsafePoly #-}
rtrnFuncUnsafePoly :: forall a b a'. (a' -> Nondet b) -> Nondet (a --> b)
rtrnFuncUnsafePoly f = pure (Func (unsafeCoerce f :: Nondet a -> Nondet b))

{-# INLINE[0] appUnsafePoly #-}
appUnsafePoly :: forall a b a'. Nondet (a --> b) -> a' -> Nondet b
appUnsafePoly mf ma = mf >>= \(Func f) -> (unsafeCoerce f :: a' -> Nondet b) ma

{-# INLINE[0] fmp #-}
fmp :: (a -> b) -> Nondet a -> Nondet b
fmp = fmap

{-# INLINE[0] shre #-}
shre :: Shareable Nondet a => Nondet a -> Nondet (Nondet a)
shre = share

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
failed = mzero

infixr 0 ?
{-# INLINE (?) #-}
-- | Nondeterministic choice
(?) :: Shareable Nondet a => Nondet (a --> a --> a)
(?) = rtrnFunc $ \t1 -> rtrnFunc $ \t2 -> t1 `mplus` t2

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
allValuesNF :: Normalform Nondet b
            => Nondet (Lifted Nondet b) -> Tree b
allValuesNF = allValues . nf

-- | Collect the results of a nondeterministic computation in a tree.
allValues :: Nondet a -> Tree a
allValues = runLazyT . unNondet

infixr 0 -->
type a --> b = (:-->) Nondet a b

-- | Lift a unary function with the lifting scheme of the plugin.
liftNondet1 :: (a -> b) -> Nondet (a --> b)
liftNondet1 f = rtrnFunc (\a -> a >>= \a' -> return (f a'))

-- | Lift a 2-ary function with the lifting scheme of the plugin.
liftNondet2 :: (a -> b -> c) -> Nondet (a --> b --> c)
liftNondet2 f = rtrnFunc (\a  -> rtrnFunc (\b  ->
                a >>=  \a' -> b >>=     \b' -> return (f a' b')))

-- | Lift a unary function with the lifting scheme of the plugin.
liftNondet1NF :: (Normalform Nondet a, Normalform Nondet b)
              => (a -> b) -> Nondet (Lifted Nondet (a -> b))
liftNondet1NF f = rtrnFunc (\a -> nf a >>= \a' -> liftE (return (f a')))

-- | Lift a 2-ary function with the lifting scheme of the plugin.
liftNondet2NF :: (Normalform Nondet a, Normalform Nondet b, Normalform Nondet c)
              => (a -> b -> c) -> Nondet (Lifted Nondet (a -> b -> c))
liftNondet2NF f = rtrnFunc (\a  -> rtrnFunc (\b  ->
                  nf a >>=  \a' -> nf b >>=     \b' -> liftE (return (f a' b'))))

-- | Apply a lifted 2-ary function to its lifted arguments.
apply2 :: Nondet (a --> b --> c) -> Nondet a -> Nondet b -> Nondet c
apply2 f a b = app f a >>= \(Func f') -> f' b

-- | Apply a lifted 2-ary function to its arguments, where just the
-- first argument has to be lifted.
apply2Unlifted :: Nondet (a --> b --> c)
               -> Nondet a -> b -> Nondet c
apply2Unlifted f a b = app f a >>= \(Func f') -> f' (return b)

-- | Apply a lifted 3-ary function to its lifted arguments.
apply3 :: Nondet (a --> b --> c --> d)
       -> Nondet a -> Nondet b -> Nondet c -> Nondet d
apply3 f a b c = apply2 f a b >>= \(Func f') -> f' c
