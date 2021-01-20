{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE LinearTypes            #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-}
{-|
Module      : Plugin.Effect.Classes
Description : Type classes used for the effect implementation
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains type classes for the nondeterminism effect,
explicit sharing and conversion between lifted and unlifted types.
The type classes are adapted from the
library explicit-sharing by Sebastian Fischer,
modernized with a generic implementation by Kai-Oliver Prott.
-}
module Plugin.Effect.Classes where

import GHC.Generics as Gen
import Data.Kind

import Plugin.Effect.Tree

-- | A class for Monads with support for explicit sharing of effects.
class Monad s => Sharing s where
  type ShareConstraints s a :: Constraint
  type ShareConstraints s a = ()
  share :: ShareConstraints s a => s a -> s (s a)

-- | A class for Nondeterminism
class Nondet n where
  failure :: n
  (?)     :: n -> n -> n

instance Nondet (Tree a) where
  failure = Failed
  (?) = Choice

-- | A class for deep sharing of nested effects.
-- For types with a generic instance, it can be derived automatically.
class Shareable m a where
  shareArgs :: (Monad n) =>
    (forall b. (Shareable m b => m b -> n (m b))) -> a -> n a
  default shareArgs :: (Gen.Generic a, ShareableGen m (Gen.Rep a), Monad n) =>
    (forall b. (Shareable m b => m b -> n (m b))) -> a -> n a
  shareArgs f a = Gen.to <$> shareArgsGen f (Gen.from a)

-- | A class for conversion between lifted and unlifted data types.
-- For types with a generic instance, it can be derived automatically.
class Monad m => Normalform m a b | a -> b, b -> a where
  -- | Convert a data type to its unlifted representation and
  -- compute its normal form.
  nf :: m a -> m b
  default nf :: ( Gen.Generic a, Gen.Generic b
                , NormalformGen m (Gen.Rep a) (Gen.Rep b))
             => m a -> m b
  nf ma = fmap Gen.to (nfGen (fmap Gen.from ma))

  -- | Convert a data type to its lifted representation.
  liftE :: m b -> m a
  default liftE :: ( Gen.Generic a, Gen.Generic b
                   , NormalformGen m (Gen.Rep a) (Gen.Rep b))
                => m b -> m a
  liftE mb = fmap Gen.to (liftEGen (fmap Gen.from mb))

-- * Generic machinery for Shareable and Normalform

class Monad m => NormalformGen m f g where
  nfGen    :: m (f x) -> m (g y)
  liftEGen :: m (g x) -> m (f y)

instance (Monad m) => NormalformGen m Gen.V1 Gen.V1 where
  nfGen _ = undefined
  liftEGen _ = undefined

instance (Monad m) => NormalformGen m Gen.U1 Gen.U1 where
  nfGen mx = mx >>= \case
    Gen.U1 -> return Gen.U1
  liftEGen mx = mx >>= \case
    Gen.U1 -> return Gen.U1

instance (Monad m, NormalformGen m f1 g1, NormalformGen m f2 g2) =>
  NormalformGen m (f1 Gen.:+: f2) (g1 Gen.:+: g2) where
    nfGen mx = mx >>= \case
      Gen.L1 x -> Gen.L1 <$> nfGen (return x)
      Gen.R1 x -> Gen.R1 <$> nfGen (return x)
    liftEGen mx = mx >>= \case
      Gen.L1 x -> Gen.L1 <$> liftEGen (return x)
      Gen.R1 x -> Gen.R1 <$> liftEGen (return x)

instance (Monad m,  NormalformGen m f1 g1, NormalformGen m f2 g2) =>
  NormalformGen m (f1 Gen.:*: f2) (g1 Gen.:*: g2) where
    nfGen mx = mx >>= \case
      x Gen.:*: y -> (Gen.:*:) <$> nfGen (return x) <*> nfGen (return y)
    liftEGen mx = mx >>= \case
      x Gen.:*: y -> (Gen.:*:) <$> liftEGen (return x) <*> liftEGen (return y)

-- | This instance overlaps the next instance.
-- Any lifted type defined by a data declaration uses this instance,
-- where we assume that the constructor arguments have the form (m b)
-- with m ~ Nondet and a Shareable instance for b
-- the other instance is used for lifted newtypes.
instance {-# OVERLAPPING #-} (Monad m, Normalform m a b) =>
  NormalformGen m (Gen.K1 i (m a)) (Gen.K1 j b) where
    nfGen mx = mx >>= \case
      Gen.K1 x -> Gen.K1 <$> nf x
    liftEGen mx = mx >>= \case
      Gen.K1 x -> Gen.K1 <$> return (liftE (return x))

-- | A lifted type defined by a newtype declaration
-- does not have a type wrapped with Nondet as its constructor argument.
-- The instance above is thus not applicable for a lifted newtype and we use
-- this one instead.
instance {-# OVERLAPPABLE #-} (Monad m, Normalform m a b) =>
  NormalformGen m (Gen.K1 i a) (Gen.K1 j b) where
    nfGen mx = mx >>= \case
      Gen.K1 x -> Gen.K1 <$> nf (return x)
    liftEGen mx = mx >>= \case
      Gen.K1 x -> Gen.K1 <$> liftE (return x)

instance (Monad m, NormalformGen m f g) =>
  NormalformGen m (Gen.M1 i t f) (Gen.M1 j h g) where
    nfGen mx = mx >>= \case
      Gen.M1 x -> Gen.M1 <$> nfGen (return x)
    liftEGen mx = mx >>= \case
      Gen.M1 x -> Gen.M1 <$> liftEGen (return x)

class ShareableGen m f where
  shareArgsGen :: (Monad n) =>
    (forall b. (Shareable m b => m b -> n (m b))) -> f x -> n (f x)

instance (Monad m) => ShareableGen m Gen.V1 where
  shareArgsGen _ _ = undefined

instance (Monad m) => ShareableGen m Gen.U1 where
  shareArgsGen _ = return

instance (Monad m, ShareableGen m f, ShareableGen m g) =>
  ShareableGen m (f Gen.:+: g) where
    shareArgsGen f (Gen.L1 x) = Gen.L1 <$> shareArgsGen f x
    shareArgsGen f (Gen.R1 x) = Gen.R1 <$> shareArgsGen f x

instance (Monad m, ShareableGen m f, ShareableGen m g) =>
  ShareableGen m (f Gen.:*: g) where
    shareArgsGen f (x Gen.:*: y) =
      (Gen.:*:) <$> shareArgsGen f x <*> shareArgsGen f y

-- | This instance overlaps the next instance.
-- Any lifted type defined by a data declaration uses this instance,
-- where we assume that the constructor arguments have the form (m b)
-- with m ~ Nondet and a Shareable instance for b
-- the other instance is used for lifted newtypes.
instance {-# OVERLAPPING #-} (Monad m, Shareable m b)
  => ShareableGen m (Gen.K1 i (m b)) where
    shareArgsGen f (Gen.K1 x) = Gen.K1 <$> f x

-- | A lifted type defined by a newtype declaration
-- does not have a type wrapped with Nondet as its constructor argument.
-- The instance above is thus not applicable for a lifted newtype and we use
-- this one instead.
instance {-# OVERLAPPABLE #-} (Monad m, Shareable m c)
  => ShareableGen m (Gen.K1 i c) where
    shareArgsGen f (Gen.K1 x) = Gen.K1 <$> shareArgs f x

instance (Monad m, ShareableGen m f) => ShareableGen m (Gen.M1 i t f) where
  shareArgsGen f (Gen.M1 x) = Gen.M1 <$> shareArgsGen f x

-- * Instances for Normalform

instance (Monad m) => Normalform m () () where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Ordering Ordering where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Bool Bool where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Int Int where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Integer Integer where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Float Float where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Double Double where
  nf    = id
  liftE = id

instance (Monad m) => Normalform m Char Char where
  nf    = id
  liftE = id

instance (Monad m, Normalform m a1 a2, Normalform m b1 b2)
  => Normalform m (m a1 -> m b1) (m a2 -> m b2) where
    nf mf = do
      f <- mf
      return $ \a -> nf (f (liftE a))
    liftE mf = do
      f <- mf
      return $ \a -> liftE (f (nf a))

-- * Instances for Shareable

instance (Monad m) => Shareable m () where
  shareArgs _ = return

instance (Monad m) => Shareable m Ordering where
  shareArgs _ = return

instance (Monad m) => Shareable m Bool where
  shareArgs _ = return

instance (Monad m) => Shareable m Int where
  shareArgs _ = return

instance (Monad m) => Shareable m Integer where
  shareArgs _ = return

instance (Monad m) => Shareable m Float where
  shareArgs _ = return

instance (Monad m) => Shareable m Double where
  shareArgs _ = return

instance (Monad m) => Shareable m Char where
  shareArgs _ = return

instance (Monad m) => Shareable m (a %n -> b) where
  shareArgs _ = return
