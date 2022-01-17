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
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}
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
import Data.Coerce

type family Lifted (m :: Type -> Type) (a :: k) = (b :: k) | b -> m a

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
class Monad m => Normalform m a where
  -- | Convert a data type to its unlifted representation and
  -- compute its normal form.
  nf :: m (Lifted m a) -> m a
  default nf :: ( Gen.Generic a, Gen.Generic (Lifted m a)
                , NormalformGen m (Gen.Rep (Lifted m a)) (Gen.Rep a))
             => m (Lifted m a) -> m a
  nf ma = fmap Gen.to (nfGen (fmap Gen.from ma))

  -- | Convert a data type to its lifted representation.
  liftE :: m a -> m (Lifted m a)
  default liftE :: ( Gen.Generic a, Gen.Generic (Lifted m a)
                   , NormalformGen m (Gen.Rep (Lifted m a)) (Gen.Rep a))
                => m a -> m (Lifted m a)
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

instance (Monad m, Lifted m b ~ a, Normalform m b) =>
  NormalformGen m (Gen.K1 i (m a)) (Gen.K1 j b) where
    nfGen mx = mx >>= \case
      Gen.K1 x -> Gen.K1 <$> nf x
    liftEGen mx = mx >>= \case
      Gen.K1 x -> Gen.K1 <$> return (liftE (return x))

instance (Monad m, NormalformGen m f g) =>
  NormalformGen m (Gen.M1 i t f) (Gen.M1 j h g) where
    nfGen mx = mx >>= \case
      Gen.M1 x -> Gen.M1 <$> nfGen (return x)
    liftEGen mx = mx >>= \case
      Gen.M1 x -> Gen.M1 <$> liftEGen (return x)

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

-- * Lifted primitives

newtype UnitND (m :: Type -> Type) = UnitND ()
type instance Lifted m () = UnitND m

newtype OrderingND (m :: Type -> Type) = OrderingND Ordering
type instance Lifted m Ordering = OrderingND m

newtype BoolND (m :: Type -> Type) = BoolND Bool
type instance Lifted m Bool = BoolND m

newtype IntND (m :: Type -> Type) = IntND Int
type instance Lifted m Int = IntND m

newtype IntegerND (m :: Type -> Type) = IntegerND Integer
type instance Lifted m Integer = IntegerND m

newtype FloatND (m :: Type -> Type) = FloatND Float
type instance Lifted m Float = FloatND m

newtype DoubleND (m :: Type -> Type) = DoubleND Double
type instance Lifted m Double = DoubleND m

newtype CharND (m :: Type -> Type) = CharND Char
type instance Lifted m Char = CharND m

infixr 0 :-->
newtype (:-->) (m :: Type -> Type) a b = Func (m a -> m b)
type instance Lifted m (->)     = (:-->) m
type instance Lifted m ((->) a) = (:-->) m (Lifted m a)
type instance Lifted m (a -> b) = (:-->) m (Lifted m a) (Lifted m b)


-- * Instances for Normalform

instance (Monad m) => Normalform m () where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Ordering where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Bool where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Int where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Integer where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Float where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Double where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Monad m) => Normalform m Char where
  nf    = fmap coerce
  liftE = fmap coerce

instance (Normalform m a, Normalform m b)
  => Normalform m ((->) a b) where
    nf    mf =
      mf >> return (error "Plugin Error: Cannot capture function types")
    liftE mf = do
      f <- mf
      return (Func (liftE . fmap f . nf))

-- * Instances for Shareable

instance (Sharing m) => Shareable m (UnitND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (OrderingND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (BoolND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (IntND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (IntegerND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (FloatND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (DoubleND m) where
  shareArgs = return

instance (Sharing m) => Shareable m (CharND m) where
  shareArgs = return

instance (Sharing m) => Shareable m ((:-->) m a b) where
  shareArgs (Func f) = fmap Func (return f)
