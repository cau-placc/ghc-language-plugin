{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE LinearTypes            #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}
{-|
Module      : Plugin.Effect.Classes
Description : Type classes used for the effect implementation
Copyright   : (c) Kai-Oliver Prott (2020 - 2023)
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

-- | A class for Monads with support for explicit sharing of effects.
class Monad s => Sharing s where
  type family ShareConstraints s a :: Constraint
  type instance ShareConstraints s a = ()
  share :: ShareConstraints s a => s a -> s (s a)

-- | A class for Monads with support for explicit sharing of top-level effects.
class Monad s => SharingTop s where
  type family ShareTopConstraints s a :: Constraint
  type instance ShareTopConstraints s a = ()
  shareTopLevel :: ShareTopConstraints s a => (Int, String) -> s a -> s a
  shareTopLevel = const id

{-# RULES
"shareTopLevel/return" forall x i. shareTopLevel i (return x) = return x
  #-}

-- | A class for deep sharing of nested effects.
-- For types with a generic instance, it can be derived automatically.
class Sharing m => Shareable m a where
  shareArgs :: a -> m a
  default shareArgs :: (Gen.Generic a, ShareableGen m (Gen.Rep a))
                    => a -> m a
  shareArgs a = Gen.to <$> shareArgsGen (Gen.from a)

-- | A class for conversion between lifted and unlifted data types.
-- For types with a generic instance, it can be derived automatically.
class Monad m => Normalform m a b | m a -> b, m b -> a where
  -- | Convert a data type to its unlifted representation and
  -- compute its normal form.
  nf :: a -> m b
  default nf :: ( Gen.Generic a, Gen.Generic b
                , NormalformGen m (Gen.Rep a) (Gen.Rep b))
             => a -> m b
  nf a = fmap Gen.to (nfGen (Gen.from a))

  -- | Convert a data type to its embedd representation.
  embed :: b -> a
  default embed :: ( Gen.Generic a, Gen.Generic b
                   , NormalformGen m (Gen.Rep a) (Gen.Rep b))
                => b -> a
  embed b = Gen.to (embedGen @m (Gen.from b))

-- * Generic machinery for Shareable and Normalform

class Monad m => NormalformGen m f g where
  nfGen    :: f x -> m (g y)
  embedGen :: g x -> f y

instance (Monad m) => NormalformGen m Gen.V1 Gen.V1 where
  nfGen _ = undefined
  embedGen _ = undefined

instance (Monad m) => NormalformGen m Gen.U1 Gen.U1 where
  nfGen x' = case x' of
    Gen.U1 -> return Gen.U1
  embedGen x' = case x' of
    Gen.U1 -> Gen.U1

instance (Monad m, NormalformGen m f1 g1, NormalformGen m f2 g2) =>
  NormalformGen m (f1 Gen.:+: f2) (g1 Gen.:+: g2) where
    nfGen x' = case x' of
      Gen.L1 x -> Gen.L1 <$> nfGen x
      Gen.R1 x -> Gen.R1 <$> nfGen x
    embedGen x' = case x' of
      Gen.L1 x -> Gen.L1 (embedGen @m x)
      Gen.R1 x -> Gen.R1 (embedGen @m x)

instance (Monad m,  NormalformGen m f1 g1, NormalformGen m f2 g2) =>
  NormalformGen m (f1 Gen.:*: f2) (g1 Gen.:*: g2) where
    nfGen x' = case x' of
      x Gen.:*: y -> (Gen.:*:) <$> nfGen x <*> nfGen y
    embedGen x' = case x' of
      x Gen.:*: y -> embedGen @m x Gen.:*: embedGen @m y

instance (Monad m, Normalform m a b) =>
  NormalformGen m (Gen.K1 i (m a)) (Gen.K1 j b) where
    nfGen x' = case x' of
      Gen.K1 x -> Gen.K1 <$> (x >>= nf)
    embedGen x' = case x' of
      Gen.K1 x -> Gen.K1 (return (embed @m x))

instance (Monad m, NormalformGen m f g) =>
  NormalformGen m (Gen.M1 i t f) (Gen.M1 j h g) where
    nfGen x' = case x' of
      Gen.M1 x -> Gen.M1 <$> nfGen x
    embedGen x' = case x' of
      Gen.M1 x -> Gen.M1 (embedGen @m x)

class Sharing m => ShareableGen m f where
  shareArgsGen :: f x -> m (f x)

instance (Sharing m) => ShareableGen m Gen.V1 where
  shareArgsGen _ = undefined

instance (Sharing m) => ShareableGen m Gen.U1 where
  shareArgsGen = return

instance (Sharing m, ShareableGen m f, ShareableGen m g) =>
  ShareableGen m (f Gen.:+: g) where
    shareArgsGen (Gen.L1 x) = Gen.L1 <$> shareArgsGen x
    shareArgsGen (Gen.R1 x) = Gen.R1 <$> shareArgsGen x

instance (Sharing m, ShareableGen m f, ShareableGen m g) =>
  ShareableGen m (f Gen.:*: g) where
    shareArgsGen (x Gen.:*: y) =
      (Gen.:*:) <$> shareArgsGen x <*> shareArgsGen y

instance (Sharing m, ShareConstraints m b) => ShareableGen m (Gen.K1 i (m b)) where
    shareArgsGen (Gen.K1 x) = Gen.K1 <$> share x

instance (Sharing m, ShareableGen m f) => ShareableGen m (Gen.M1 i t f) where
  shareArgsGen (Gen.M1 x) = Gen.M1 <$> shareArgsGen x

-- * Instances for Normalform

instance (Monad m) => Normalform m () () where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Ordering Ordering where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Bool Bool where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Int Int where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Integer Integer where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Float Float where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Double Double where
  nf    = return
  embed = id

instance (Monad m) => Normalform m Char Char where
  nf    = return
  embed = id

-- * Instances for Shareable

instance (Sharing m) => Shareable m () where
  shareArgs = return

instance (Sharing m) => Shareable m Ordering where
  shareArgs = return

instance (Sharing m) => Shareable m Bool where
  shareArgs = return

instance (Sharing m) => Shareable m Int where
  shareArgs = return

instance (Sharing m) => Shareable m Integer where
  shareArgs = return

instance (Sharing m) => Shareable m Float where
  shareArgs = return

instance (Sharing m) => Shareable m Double where
  shareArgs = return

instance (Sharing m) => Shareable m Char where
  shareArgs = return

instance (Sharing m) => Shareable m (a %n -> b) where
  shareArgs = return
