{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
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
module Plugin.CurryPlugin.Free where

import Control.Applicative
import Control.Monad
import Unsafe.Coerce
import Prelude hiding (fail)

import Plugin.Effect.Classes

{-# INLINE[0] bind #-}
bind :: Functor sig => Free sig a -> (a -> Free sig b) -> Free sig b
bind = (>>=)

{-# INLINE[0] rtrn #-}
rtrn :: Functor sig => a -> Free sig a
rtrn = pure

{-# INLINE[0] rtrnFunc #-}
rtrnFunc :: Functor sig => (Free sig a -> Free sig b) -> Free sig ((:-->) (Free sig) a b)
rtrnFunc = pure . Func

{-# INLINE[0] app #-}
app :: Functor sig => Free sig ((:-->) (Free sig) a b) -> Free sig a -> Free sig b
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
rtrnFuncUnsafePoly :: forall a b a' sig. Functor sig => (a' -> Free sig b) -> Free sig ((:-->) (Free sig) a b)
rtrnFuncUnsafePoly f = pure (Func (unsafeCoerce f :: Free sig a -> Free sig b))

{-# INLINE[0] appUnsafePoly #-}
appUnsafePoly :: forall a b a' sig. Functor sig => Free sig ((:-->) (Free sig) a b) -> a' -> Free sig b
appUnsafePoly mf ma = mf >>= \(Func f) -> (unsafeCoerce f :: a' -> Free sig b) ma

{-# INLINE[0] fmp #-}
fmp :: Functor sig => (a -> b) -> Free sig a -> Free sig b
fmp = fmap

{-# INLINE[0] shre #-}
shre :: (Functor sig, Shareable (Free sig) a) => Free sig a -> Free sig (Free sig a)
shre = share

{-# INLINE[0] shreTopLevel #-}
shreTopLevel :: Functor sig => (Int, String) -> Free sig a -> Free sig a
shreTopLevel = shareTopLevel

{-# INLINE seqValue #-}
seqValue :: Functor sig => Free sig a -> Free sig b -> Free sig b
seqValue a b = a >>= \a' -> a' `seq` b

-- Free monad

data Free sig a
  = Var a
  | Op (sig (Free sig a))
  deriving stock (Functor)
  deriving anyclass (SharingTop)

instance Functor sig => Applicative (Free sig) where
  pure = Var
  (<*>) = ap

instance (Functor sig) => Monad (Free sig) where
  Var x >>= f = f x
  Op op >>= f = Op (fmap (>>= f) op)

instance Functor sig => Sharing (Free sig) where 
  share = (>>= return . return)

foldFree :: Functor sig => (a -> b) -> (sig b -> b) -> Free sig a -> b
foldFree var _ (Var x) = var x
foldFree var op (Op sig) = op (fmap (foldFree var op) sig)

-- Signature functors

data None a
  deriving (Functor)

data (sig1 :+: sig2) a = Inl (sig1 a) | Inr (sig2 a)
  deriving (Functor)

infixr 0 :+:

(\/) :: (sig1 b -> b) -> (sig2 b -> b) -> (sig1 :+: sig2) b -> b
( alg1 \/ _alg2) (Inl op) = alg1 op
(_alg1 \/  alg2) (Inr op) = alg2 op

infixr 5 \/

-- Effect injection

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance {-# OVERLAPPING #-} (Functor sig1, Functor sig2) => sig1 :<: (sig1 :+: sig2) where
  inj = Inl
  prj (Inl sig) = Just sig
  prj _ = Nothing

instance {-# OVERLAPPABLE #-} (Functor sig1, sig :<: sig2) => sig :<: (sig1 :+: sig2) where
  inj = Inr . inj
  prj (Inr sig) = prj sig
  prj _ = Nothing

inject :: (sub :<: sup) => sub (Free sup a) -> Free sup a
inject = Op . inj

run :: Free None a -> a
run (Var x) = x
run (Op sig) = case sig of

-- | Lift a unary function with the lifting scheme of the plugin.
liftNondet1 :: Functor sig => (a -> b) -> Free sig ((:-->) (Free sig) a b)
liftNondet1 f = rtrnFunc (\a -> a >>= \a' -> return (f a'))

-- | Lift a 2-ary function with the lifting scheme of the plugin.
liftNondet2 :: Functor sig => (a -> b -> c) -> Free sig ((:-->) (Free sig) a ((:-->) (Free sig) b c))
liftNondet2 f = rtrnFunc (\a  -> rtrnFunc (\b  ->
                a >>=  \a' -> b >>=     \b' -> return (f a' b')))

-- | Lift a unary function with the lifting scheme of the plugin.
liftNondet1NF :: (Normalform (Free sig) a, Normalform (Free sig) b, Functor sig)
              => (a -> b) -> Free sig (Lifted (Free sig) (a -> b))
liftNondet1NF f = rtrnFunc (\a -> nf a >>= \a' -> liftE (return (f a')))

-- | Lift a 2-ary function with the lifting scheme of the plugin.
liftNondet2NF :: (Normalform (Free sig) a, Normalform (Free sig) b, Normalform (Free sig) c, Functor sig)
              => (a -> b -> c) -> Free sig (Lifted (Free sig) (a -> b -> c))
liftNondet2NF f = rtrnFunc (\a  -> rtrnFunc (\b  ->
                  nf a >>=  \a' -> nf b >>=     \b' -> liftE (return (f a' b'))))

-- | Apply a lifted 2-ary function to its lifted arguments.
apply2 :: Functor sig => Free sig ((:-->) (Free sig) a ((:-->) (Free sig) b c)) -> Free sig a -> Free sig b -> Free sig c
apply2 f a b = app f a >>= \(Func f') -> f' b

-- | Apply a lifted 2-ary function to its arguments, where just the
-- first argument has to be lifted.
apply2Unlifted :: Functor sig => Free sig ((:-->) (Free sig) a ((:-->) (Free sig) b c))
               -> Free sig a -> b -> Free sig c
apply2Unlifted f a b = app f a >>= \(Func f') -> f' (return b)

-- | Apply a lifted 3-ary function to its lifted arguments.
apply3 :: Functor sig => Free sig ((:-->) (Free sig) a ((:-->) (Free sig) b ((:-->) (Free sig) c d)))
       -> Free sig a -> Free sig b -> Free sig c -> Free sig d
apply3 f a b c = apply2 f a b >>= \(Func f') -> f' c
