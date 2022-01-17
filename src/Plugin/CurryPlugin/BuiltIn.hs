{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-orphans        #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
{-|
Module      : Plugin.CurryPlugin.BuiltIn
Description : Built-In functions, types and type classes
Copyright   : (c) Kai-Oliver Prott (2020)
License     : BSD-3 Clause
Maintainer  : kai.prott@hotmail.de

This module contains lifted replacements for data types, functions
and type classes for Haskell's default Prelude.
This module is not supposed to be imported by users, please import
'Plugin.CurryPlugin.Prelude' instead.
-}
module Plugin.CurryPlugin.BuiltIn where

import qualified Prelude                as P
import           Prelude                     ( ($), Bool(..), Ordering(..) )
import qualified GHC.Real               as P
import qualified GHC.Prim               as P
import qualified GHC.Int                as P
import           Unsafe.Coerce
import           GHC.Types                   ( RuntimeRep, Multiplicity )

import Plugin.CurryPlugin.Monad
import Plugin.Effect.Classes

-- | Alias for Shareable constraint specialized to the nondeterminism monad.
type ShareableN a = Shareable Nondet a

-- | This is a lifted version of the unrestricted function type constructor
type (:--->) m r s a b = (:-->) m a b

-- | This is a lifted version of the multiplicity-augmented (unrestricted) function type constructor
type (:--->#) m mult r s a b = (:-->) m a b

-- * Lifted list type and internal instances

-- | Lifted defintion for Haskell's default list type '[]'
data ListND m a = Nil | Cons (m a) (m (ListND m a))

type instance Lifted m [] = ListND m
type instance Lifted m [a] = ListND m (Lifted m a)

-- | Lifted smart constructor for 'Nil'
nil :: Nondet (ListND Nondet a)
nil = P.return Nil

-- | Lifted smart constructor for 'Cons'
cons :: Nondet (a --> ListND Nondet a --> ListND Nondet a)
cons = rtrnFunc $ \a -> rtrnFunc $ \as -> P.return (Cons a as)

-- | Shareable instance for lists.
instance (ShareConstraints m a, ShareConstraints m (ListND m a), Sharing m) =>
  Shareable m (ListND m a) where
    shareArgs Nil         = P.return Nil
    shareArgs (Cons x xs) = Cons P.<$> share x P.<*> share xs

-- | Normalform instance for lists
instance (P.Monad m, Normalform m a) => Normalform m [a] where
  nf mxs = mxs P.>>= \case
    Nil       -> P.return []
    Cons x xs -> (:) P.<$> nf x P.<*> nf xs
  liftE mxs = mxs P.>>= \case
    []   -> P.return Nil
    x:xs -> Cons P.<$> P.return (liftE (P.return x))
                 P.<*> P.return (liftE (P.return xs))

-- * Lifted tuple types and internal instances

-- | Lifted defintion for Haskell's 2-ary tuple '(,)'
data Tuple2ND m a b = Tuple2 (m a) (m b)

type instance Lifted m (,)     = Tuple2ND m
type instance Lifted m ((,) a) = Tuple2ND m (Lifted m a)
type instance Lifted m (a, b)  = Tuple2ND m (Lifted m a) (Lifted m b)

-- | Selector for the first component of a lifted 2-ary tuple
fst :: Nondet (Tuple2ND Nondet a b --> a)
fst = rtrnFunc $ \t -> t P.>>= \(Tuple2 a _) -> a

-- | Selector for the second component of a lifted 2-ary tuple
snd :: Nondet (Tuple2ND Nondet a b --> b)
snd = rtrnFunc $ \t -> t P.>>= \(Tuple2 _ b) -> b

-- | Shareable instance for 2-ary tuple
instance (ShareConstraints m a, ShareConstraints m b, Sharing m) =>
  Shareable m (Tuple2ND m a b) where
    shareArgs (Tuple2 a b) = Tuple2 P.<$> share a P.<*> share b

-- | Normalform instance for 2-ary tuple
instance (P.Monad m, Normalform m a, Normalform m b) =>
  Normalform m (a, b) where
    nf mxs = mxs P.>>= \(Tuple2 a b) -> (,) P.<$> nf a P.<*> nf b
    liftE mxs = mxs P.>>= \(a, b) -> Tuple2 P.<$> P.return (liftE (P.return a))
                                            P.<*> P.return (liftE (P.return b))

-- * Other lifted types and internal instances

-- | Lifted defintion for Haskell's 'String' type
type StringND m = ListND m (CharND m)

-- | Lifted defintion for Haskell's 'Ratio' type
data RatioND m a = !(m a) :% !(m a)

type instance Lifted m P.Ratio = RatioND m
type instance Lifted m (P.Ratio a) = RatioND m (Lifted m a)

-- | Shareable instance for Ratios
instance (ShareConstraints m a, Sharing m) =>
  Shareable m (RatioND m a) where
    shareArgs (a :% b) = (:%) P.<$> share a P.<*> share b

-- | Normalform instance for Ratios
instance (P.Monad m, Normalform m a) =>
  Normalform m (P.Ratio a) where
    nf mxs = mxs P.>>= \(a :% b) -> (P.:%) P.<$> nf a P.<*> nf b
    liftE mxs = mxs P.>>= \(a P.:% b) ->
      (:%) P.<$> P.return (liftE (P.return a))
           P.<*> P.return (liftE (P.return b))

-- | Lifted defintion for Haskell's 'Rational' type
type RationalND m = RatioND m (IntegerND m)


-- * Lifted functions

-- $liftedFunctions
-- The pre-lifted functions are used to desugar
-- do-notation, (list) comprehensions or to replace their Haskell counterpart
-- in derived instances.

-- | Function to use for pattern match failures
-- Pattern match failure is translated to a failed for Curry,
-- ignoring the string.
pE :: ShareableN a => Nondet (StringND Nondet --> a)
pE = rtrnFunc (P.>>= P.const failed)

-- | Lifted identity function
id :: Nondet (a --> a)
id = rtrnFunc P.id

-- | Lifted logical negation
not :: Nondet (BoolND Nondet --> BoolND Nondet)
not = liftNondet1NF P.not

-- Note: In order to be able to keep all type-applications
-- of the original code for the following "primops",
-- we introduce the same number and order of type variables,
-- even if they are unused

-- Lifted seq operator to force evaluation. Forces the effect and value.
seq :: forall (k :: RuntimeRep) a b. Nondet (a --> b --> b)
seq = rtrnFunc $ \a -> rtrnFunc $ \b ->
  (a P.>>= \a' -> P.seq a' b)

-- Lifted function to desugar left sections.
leftSection :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep)
                      (n :: Multiplicity) a b.
               Nondet ((a --> b) --> a --> b)
leftSection = rtrnFunc $ \f -> rtrnFunc $ \a ->
  f `app` a

-- Lifted function to desugar right sections.
rightSection :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep) (r3 :: RuntimeRep)
                       (n1 :: Multiplicity) (n2 :: Multiplicity) a b c.
                Nondet ((a --> b --> c) --> b --> a --> c)
rightSection = rtrnFunc $ \f -> rtrnFunc $ \b -> rtrnFunc $ \a ->
  f `app` a `app` b

-- | Lifted const function
const :: Nondet (a --> b --> a)
const = rtrnFunc $ \a -> rtrnFunc $ \_ -> a

-- | Lifted logical and
(&&) :: Nondet (BoolND Nondet --> BoolND Nondet --> BoolND Nondet)
(&&) =  rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> a1 P.>>= \case
  BoolND False -> P.return (BoolND False)
  BoolND True  -> a2

-- | Lifted guard function used to desugar monad comprehensions
guard :: (AlternativeND f, forall x . ShareableN x => ShareableN (f x))
      => Nondet (BoolND Nondet --> f (UnitND Nondet))
guard = rtrnFunc $ \b -> b P.>>= \case
  BoolND True  -> pure `app` (P.return (UnitND ()))
  BoolND False -> empty

-- | Lifted append function for lists
append :: ShareableN a => Nondet (ListND Nondet a --> ListND Nondet a --> ListND Nondet a)
append = rtrnFunc $ \xs -> rtrnFunc $ \ys -> xs P.>>= \case
  Nil       -> ys
  Cons a as -> P.return (Cons a (apply2 append as ys))

-- | Lifted concatMap function for lists
concatMap :: (ShareableN a, ShareableN b)
          => Nondet ((a --> ListND Nondet b) --> ListND Nondet a --> ListND Nondet b)
concatMap = rtrnFunc $ \f -> rtrnFunc $ \xs -> xs P.>>= \case
  Nil       -> P.return Nil
  Cons a as -> append `app` (f `app` a) `app` (concatMap `app` f `app` as)

-- | Lifted map function for lists
map :: Nondet ((a --> b) --> ListND Nondet a --> ListND Nondet b)
map = rtrnFunc $ \f' -> share f' P.>>= \f ->
  rtrnFunc $ \xs -> xs P.>>= \case
  Nil       -> P.return Nil
  Cons a as -> P.return (Cons (f `app` a) (apply2 map f as))

-- | Lifted coercion function to replace coercion in newtype-derived instances
-- We need to introduce this unused dummy k,
-- because we replace Data.Coerce.coerce (which has this k).
coerce :: forall (k :: RuntimeRep) a b. (ShareableN a, ShareableN b)
       => Nondet (a --> b)
coerce = rtrnFunc $ \a -> a P.>>= \a' -> P.return (unsafeCoerce a')

-- | Lifted equality test for strings
eqString :: Nondet (StringND Nondet --> StringND Nondet --> BoolND Nondet)
eqString = (==)

(<#) :: Nondet (IntND Nondet --> IntND Nondet --> IntND Nondet)
(<#) = rtrnFunc $ \a -> rtrnFunc $ \b ->
  a P.>>= \ (IntND (P.I# a')) -> b P.>>= \ (IntND (P.I# b')) ->
   P.return (IntND (P.I# (a' P.<# b')))

(==#) :: Nondet (IntND Nondet --> IntND Nondet --> IntND Nondet)
(==#) = rtrnFunc $ \a -> rtrnFunc $ \b ->
  a P.>>= \ (IntND (P.I# a')) -> b P.>>= \ (IntND (P.I# b')) ->
  P.return (IntND (P.I# (a' P.==# b')))

-- |  Lifted composition operator for functions
(.) :: (ShareableN a, ShareableN b, ShareableN c)
    => Nondet ((b --> c) --> (a --> b) --> a --> c)
(.) = rtrnFunc $ \f1 -> rtrnFunc $ \f2 -> rtrnFunc $ \a ->
  f1 `app` (f2 `app` a)

-- * Lifted Show type class, instances and functions

-- | Lifted ShowS type
type ShowSND m = (:-->) m (StringND m) (StringND m)

-- | Lifted Show type class
class ShowND a where
  {-# MINIMAL showsPrec | show #-}
  showsPrec :: Nondet (IntND Nondet --> a --> ShowSND Nondet)
  showsPrec = rtrnFunc $ \_ -> rtrnFunc $ \x -> rtrnFunc $ \s ->
    apply2 append (show `app` x) s

  show :: Nondet (a --> StringND Nondet)
  show = rtrnFunc $ \x -> apply2 shows x (P.return Nil)

  showList :: Nondet (ListND Nondet a --> ShowSND Nondet)
  showList = rtrnFunc $ \ls -> rtrnFunc $ \s -> apply3 showsList__ shows ls s

showsList__ :: Nondet ((a --> ShowSND Nondet) --> ListND Nondet a --> ShowSND Nondet)
showsList__ = rtrnFunc $ \showx -> rtrnFunc $ \list -> rtrnFunc $ \s ->
  list P.>>= \case
    Nil       -> apply2 append (liftE (P.return "[]")) s
    Cons x xs ->
      P.return (Cons (liftE (P.return '[')) (apply2 showx x (apply3 showl showx xs s)))
  where
    showl = rtrnFunc $ \showx -> rtrnFunc $ \list -> rtrnFunc $ \s ->
      list P.>>= \case
        Nil       ->
          P.return (Cons (liftE (P.return ']')) s)
        Cons y ys ->
          P.return (Cons (liftE (P.return ','))
            (apply2 showx y (apply3 showl showx ys s)))

shows :: ShowND a => Nondet (a --> ShowSND Nondet)
shows = showsPrec `app` (liftE $ P.return 0)

showString :: Nondet (StringND Nondet --> ShowSND Nondet)
showString = append

showCommaSpace :: Nondet (ShowSND Nondet)
showCommaSpace = showString `app` (liftE (P.return ", "))

showSpace :: Nondet (ShowSND Nondet)
showSpace =  showString `app` (liftE (P.return " "))

showParen :: Nondet (BoolND Nondet --> ShowSND Nondet --> ShowSND Nondet)
showParen = rtrnFunc $ \b -> rtrnFunc $ \s -> b P.>>= \case
  BoolND True  -> apply2 (.) (showString `app` (liftE (P.return "(")))
          (apply2 (.) s (showString `app` (liftE (P.return ")"))))
  BoolND False -> s

instance ShowND (BoolND Nondet) where
  show = liftNondet1NF P.show

instance ShowND (UnitND Nondet) where
  show = liftNondet1NF P.show

instance ShowND (IntND Nondet) where
  show = liftNondet1NF P.show

instance ShowND (IntegerND Nondet) where
  show = liftNondet1NF P.show

instance ShowND (FloatND Nondet) where
  show = liftNondet1NF P.show

instance ShowND (DoubleND Nondet) where
  show = liftNondet1NF P.show

instance ShowND (CharND Nondet) where
  show = liftNondet1NF P.show
  showList = liftNondet1NF P.showList

instance (ShowND a, ShareableN a) => ShowND (ListND Nondet a) where
  show = rtrnFunc $ \xs -> apply2 showList xs (P.return Nil)

-- * Lifted Eq type class, instances and functions

-- | Lifted Eq type class
class EqND a where
  (==) :: Nondet (a --> a --> BoolND Nondet)
  (==) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> not `app` (apply2 (/=) a1 a2)

  (/=) :: Nondet (a --> a --> BoolND Nondet)
  (/=) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> not `app` (apply2 (==) a1 a2)

instance EqND (BoolND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance EqND (UnitND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance EqND (IntND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance EqND (IntegerND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance EqND (FloatND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance EqND (DoubleND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance EqND (CharND Nondet) where
  (==) = liftNondet2NF (P.==)
  (/=) = liftNondet2NF (P./=)

instance (EqND a, ShareableN a) => EqND (ListND Nondet a) where
  (==) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> a1 P.>>= \case
    Nil       -> a2 P.>>= \case
      Nil       -> P.return $ BoolND True
      Cons _ _  -> P.return $ BoolND False
    Cons x xs -> a2 P.>>= \case
      Nil       -> P.return $ BoolND False
      Cons y ys -> eqOn2 x y xs ys

instance (EqND a, EqND b, ShareableN a, ShareableN b) =>
  EqND (Tuple2ND Nondet a b) where
  (==) = rtrnFunc $ \x1 -> rtrnFunc $ \x2 -> do
    (Tuple2 a1 b1) <- x1
    (Tuple2 a2 b2) <- x2
    eqOn2 a1 a2 b1 b2

instance (EqND a, ShareableN a) => EqND (RatioND Nondet a) where
  (==) = rtrnFunc $ \x1 -> rtrnFunc $ \x2 -> do
    (a1 :% b1) <- x1
    (a2 :% b2) <- x2
    eqOn2 a1 a2 b1 b2

eqOn2 :: (EqND a1, EqND a2, ShareableN a1, ShareableN a2)
     => Nondet a1 -> Nondet a1 -> Nondet a2 -> Nondet a2 -> Nondet (BoolND Nondet)
eqOn2 x y xs ys = apply2 (&&) (apply2 (==) x y) (apply2 (==) xs ys)

-- * Lifted Ord type class, instances and functions

-- | Lifted Ord type class
class EqND a => OrdND a where
  {-# MINIMAL compare | (<=) #-}
  compare :: Nondet (a --> a --> OrderingND Nondet)
  compare = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
    apply2 (==) a1 a2 P.>>= \(BoolND b1) -> if b1
      then P.return (OrderingND EQ)
      else apply2 (<=) a1 a2 P.>>= \(BoolND b2) -> if b2
        then P.return $ OrderingND LT
        else P.return $ OrderingND GT

  (<) :: Nondet (a --> a --> BoolND Nondet)
  (<) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
    apply2 compare a1 a2 P.>>= \case
      OrderingND LT -> P.return $ BoolND True
      _             -> P.return $ BoolND False

  (<=) :: Nondet (a --> a --> BoolND Nondet)
  (<=) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
    apply2 compare a1 a2 P.>>= \case
      OrderingND GT -> P.return $ BoolND False
      _             -> P.return $ BoolND True

  (>) :: Nondet (a --> a --> BoolND Nondet)
  (>) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
    apply2 compare a1 a2 P.>>= \case
      OrderingND GT -> P.return $ BoolND True
      _             -> P.return $ BoolND False

  (>=) :: Nondet (a --> a --> BoolND Nondet)
  (>=) = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
    apply2 compare a1 a2 P.>>= \case
      OrderingND LT -> P.return $ BoolND False
      _             -> P.return $ BoolND True

  -- This default implementation is replaced at compile-time with maxDefault
  max :: Nondet (a --> a --> a)
  max = P.undefined

  -- This default implementation is replaced at compile-time with minDefault
  min :: Nondet (a --> a --> a)
  min = P.undefined

maxDefault :: (OrdND a, ShareableN a) => Nondet (a --> a --> a)
maxDefault = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
  share a1 P.>>= \a1' -> share a2 P.>>= \a2' ->
  apply2 (>=) a1' a2' P.>>= \case
    BoolND True -> a1'
    _           -> a2'

minDefault :: (OrdND a, ShareableN a) => Nondet (a --> a --> a)
minDefault = rtrnFunc $ \a1 -> rtrnFunc $ \a2 ->
  share a1 P.>>= \a1' -> share a2 P.>>= \a2' ->
  apply2 (<=) a1' a2' P.>>= \case
    BoolND True -> a1'
    _           -> a2'

instance OrdND (BoolND Nondet) where
  compare = liftNondet2NF P.compare

instance OrdND (UnitND Nondet) where
  compare = liftNondet2NF P.compare

instance OrdND (IntND Nondet) where
  compare = liftNondet2NF P.compare

instance OrdND (IntegerND Nondet) where
  compare = liftNondet2NF P.compare

instance OrdND (FloatND Nondet) where
  compare = liftNondet2NF P.compare

instance OrdND (DoubleND Nondet) where
  compare = liftNondet2NF P.compare

instance (OrdND a, ShareableN a) => OrdND (ListND Nondet a) where
  compare = rtrnFunc $ \x -> rtrnFunc $ \y ->
    x P.>>= \x' -> y P.>>= \y' -> case (x', y') of
      (Nil      , Nil      ) -> P.return (OrderingND EQ)
      (Nil      , Cons _ _ ) -> P.return (OrderingND LT)
      (Cons _ _ , Nil      ) -> P.return (OrderingND GT)
      (Cons a as, Cons b bs) -> apply2 compare a b P.>>= \case
        OrderingND EQ -> apply2 compare as bs
        o  -> P.return o

instance (OrdND a, OrdND b, ShareableN a, ShareableN b) =>
  OrdND (Tuple2ND Nondet a b) where
  compare = rtrnFunc $ \x -> rtrnFunc $ \y ->
    x P.>>= \x' -> y P.>>= \y' -> case (x', y') of
      (Tuple2 a1 b1, Tuple2 a2 b2) -> apply2 compare a1 a2 P.>>= \case
        OrderingND EQ -> apply2 compare b1 b2
        o  -> P.return o

-- * Lifted Num type class, instances and functions

-- | Lifted Num type class
class NumND a where
  (+) :: Nondet (a --> a --> a)
  (-) :: Nondet (a --> a --> a)
  (-) = rtrnFunc $ \a -> rtrnFunc $ \b ->
    (+) `app` a `app` (negate `app` b)
  (*) :: Nondet (a --> a --> a)
  negate :: Nondet (a --> a)
  negate = rtrnFunc $ \a -> (-) `app` (fromInteger `app` (liftE (P.return 0))) `app` a
  abs    :: Nondet (a --> a)
  signum :: Nondet (a --> a)
  fromInteger :: Nondet (IntegerND Nondet --> a)

instance NumND (IntND Nondet) where
  (+) = liftNondet2NF (P.+)
  (-) = liftNondet2NF (P.-)
  (*) = liftNondet2NF (P.*)
  negate = liftNondet1NF P.negate
  abs    = liftNondet1NF P.abs
  signum = liftNondet1NF P.signum
  fromInteger = liftNondet1NF P.fromInteger

instance NumND (IntegerND Nondet) where
  (+) = liftNondet2NF (P.+)
  (-) = liftNondet2NF (P.-)
  (*) = liftNondet2NF (P.*)
  negate = liftNondet1NF P.negate
  abs    = liftNondet1NF P.abs
  signum = liftNondet1NF P.signum
  fromInteger = liftNondet1NF P.fromInteger

instance NumND (FloatND Nondet) where
  (+) = liftNondet2NF (P.+)
  (-) = liftNondet2NF (P.-)
  (*) = liftNondet2NF (P.*)
  negate = liftNondet1NF P.negate
  abs    = liftNondet1NF P.abs
  signum = liftNondet1NF P.signum
  fromInteger = liftNondet1NF P.fromInteger

instance NumND (DoubleND Nondet) where
  (+) = liftNondet2NF (P.+)
  (-) = liftNondet2NF (P.-)
  (*) = liftNondet2NF (P.*)
  negate = liftNondet1NF P.negate
  abs    = liftNondet1NF P.abs
  signum = liftNondet1NF P.signum
  fromInteger = liftNondet1NF P.fromInteger

-- * Lifted Fractional type class, instances and functions

-- | Lifted Fractional type class
class NumND a => FractionalND a where
  {-# MINIMAL fromRational, (recip | (/)) #-}

  (/) :: Nondet (a --> a --> a)
  (/) = rtrnFunc $ \x -> rtrnFunc $ \y -> apply2 (*) x  (recip `app` y)

  recip :: Nondet (a --> a)
  recip = rtrnFunc $ \x -> apply2 (/) (fromInteger `app` (liftE (P.return 1))) x

  fromRational :: Nondet (RationalND Nondet --> a)

instance FractionalND (FloatND Nondet) where
  (/) = liftNondet2NF (P./)
  fromRational = liftNondet1NF P.fromRational

instance FractionalND (DoubleND Nondet) where
  (/) = liftNondet2NF (P./)
  fromRational = liftNondet1NF P.fromRational

-- * Lifted Real type class, instances and functions

-- | Lifted Real type class
class (NumND a, OrdND a) => RealND a where
  toRational :: Nondet (a --> RationalND Nondet)

instance RealND (IntND Nondet) where
  toRational = liftNondet1NF P.toRational

instance RealND (IntegerND Nondet) where
  toRational = liftNondet1NF P.toRational

instance RealND (FloatND Nondet) where
  toRational = liftNondet1NF P.toRational

instance RealND (DoubleND Nondet) where
  toRational = liftNondet1NF P.toRational

-- * Lifted Integral type class, instances and functions

-- | Lifted Integral type class
class (RealND a, EnumND a) => IntegralND a where
  quot      :: Nondet (a --> a --> a)
  rem       :: Nondet (a --> a --> a)
  div       :: Nondet (a --> a --> a)
  mod       :: Nondet (a --> a --> a)
  quotRem   :: Nondet (a --> a --> Tuple2ND Nondet a a)
  divMod    :: Nondet (a --> a --> Tuple2ND Nondet a a)
  toInteger :: Nondet (a --> IntegerND Nondet)

  quot   = rtrnFunc $ \n -> rtrnFunc $ \d -> fst `app` (apply2 quotRem n d)
  rem    = rtrnFunc $ \n -> rtrnFunc $ \d -> snd `app` (apply2 quotRem n d)
  div    = rtrnFunc $ \n -> rtrnFunc $ \d -> fst `app` (apply2 divMod n d)
  mod    = rtrnFunc $ \n -> rtrnFunc $ \d -> snd `app` (apply2 divMod n d)

  -- This default implementation is replaced at compile-time with divModDefault
  divMod = P.undefined

divModDefault :: (IntegralND a, ShareableN a)
              => Nondet (a --> a --> Tuple2ND Nondet a a)
divModDefault = rtrnFunc $ \n' -> rtrnFunc $ \d' ->
  share n' P.>>= \n -> share d' P.>>= \d ->
  let qr' = apply2 quotRem n d
  in share qr' P.>>= \qr ->
     qr P.>>= \(Tuple2 q r) -> apply2 (==) (signum `app` r)
                                           (negate `app` (signum `app` d))
        P.>>= \(BoolND b) -> if b
          then P.return (Tuple2 (apply2 (-) q
                                   (fromInteger `app` (liftE (P.return 1))))
                                   (apply2 (+) r d))
          else qr

instance IntegralND (IntND Nondet) where
  quot = liftNondet2NF (P.quot)
  rem  = liftNondet2NF (P.rem)
  div  = liftNondet2NF (P.div)
  mod  = liftNondet2NF (P.mod)

  quotRem = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> do
    IntND v1 <- a1
    IntND v2 <- a2
    liftE (P.return (P.quotRem v1 v2))
  divMod = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> do
    IntND v1 <- a1
    IntND v2 <- a2
    liftE (P.return (P.divMod v1 v2))

  toInteger = liftNondet1NF (P.toInteger)

instance IntegralND (IntegerND Nondet) where
  quot = liftNondet2NF (P.quot)
  rem  = liftNondet2NF (P.rem)
  div  = liftNondet2NF (P.div)
  mod  = liftNondet2NF (P.mod)

  quotRem = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> do
    IntegerND v1 <- a1
    IntegerND v2 <- a2
    liftE (P.return (P.quotRem v1 v2))
  divMod = rtrnFunc $ \a1 -> rtrnFunc $ \a2 -> do
    IntegerND v1 <- a1
    IntegerND v2 <- a2
    liftE (P.return (P.divMod v1 v2))

  toInteger = rtrnFunc P.id

-- * Lifted Monad & Co type classes and instances

infixl 1 >>=, >>
infixl 4 <$, <*, *>, <*>
-- | Lifted Functor type class
class FunctorND f where
  fmap :: (ShareableN a, ShareableN b) => Nondet ((a --> b) --> f a --> f b)
  (<$) :: (ShareableN a, ShareableN b) => Nondet (a --> f b --> f a)
  (<$) = rtrnFunc $ \a -> rtrnFunc $ \f ->
    apply2 fmap (const `app` a) f

instance FunctorND (Tuple2ND Nondet a) where
  fmap = rtrnFunc $ \f -> rtrnFunc $ \t -> t P.>>= \case
    Tuple2 a b -> P.return (Tuple2 a (f `app` b))

instance FunctorND (ListND Nondet) where
  fmap = rtrnFunc $ \f -> rtrnFunc $ \l -> l P.>>= \case
    Nil       -> P.return Nil
    Cons x xs -> P.return (Cons (f `app` x) (apply2 fmap f xs))

-- | Lifted Applicative type class
class FunctorND f => ApplicativeND f where
  pure :: ShareableN a => Nondet (a --> f a)

  (<*>) :: (ShareableN a, ShareableN b) => Nondet (f (a --> b) --> f a --> f b)
  (<*>) = rtrnFunc $ \f -> rtrnFunc $ \a ->
    apply3 liftA2 (liftNondet1 P.id) f a

  liftA2 :: (ShareableN a, ShareableN b, ShareableN c)
         => Nondet ((a --> b --> c) --> f a --> f b --> f c)
  liftA2 = rtrnFunc $ \f -> rtrnFunc $ \a -> rtrnFunc $ \b ->
    apply2 (<*>) (apply2 fmap f a) b

  (*>) :: (ShareableN a, ShareableN b) => Nondet (f a --> f b --> f b)
  (*>) = rtrnFunc $ \a -> rtrnFunc $ \b ->
    apply3 liftA2 (liftNondet2 (P.flip P.const)) a b

  (<*) :: (ShareableN a, ShareableN b) => Nondet (f a --> f b --> f a)
  (<*) = rtrnFunc $ \a -> rtrnFunc $ \b ->
    apply3 liftA2 const a b
  {-# MINIMAL pure, ((<*>) | liftA2) #-}

instance ApplicativeND (ListND Nondet) where
  pure = rtrnFunc $ \a -> P.return (Cons a (P.return Nil))
  (<*>) = rtrnFunc $ \fs -> rtrnFunc $ \as ->
    apply2 concatMap (rtrnFunc $ \a ->
    apply2 fmap      (rtrnFunc $ \f -> f `app` a) fs) as

  -- | Lifted Alternative type class
class ApplicativeND f => AlternativeND f where
  empty :: ShareableN a => Nondet (f a)
  (<|>) :: ShareableN a => Nondet (f a --> f a --> f a)
  some  :: ShareableN a => Nondet (f a --> f (ListND Nondet a))
  some = rtrnFunc $ \v ->
    let many_v = apply2 (<|>) some_v (pure `app` (P.return Nil))
        some_v = apply3 liftA2 cons v many_v
    in some_v
  many  :: ShareableN a => Nondet (f a --> f (ListND Nondet a))
  many = rtrnFunc $ \v ->
    let many_v = apply2 (<|>) some_v (pure `app` (P.return Nil))
        some_v = apply3 liftA2 cons v many_v
    in many_v

instance AlternativeND (ListND Nondet) where
  empty = nil
  (<|>) = append

-- | Lifted Monad type class
class ApplicativeND m => MonadND m where
  (>>=) :: (ShareableN a, ShareableN b) => Nondet (m a --> (a --> m b) --> m b)
  (>>)  :: (ShareableN a, ShareableN b) => Nondet (m a --> m b --> m b)
  (>>) = rtrnFunc $ \a -> rtrnFunc $ \b ->
    apply2 (>>=) a (rtrnFunc (P.const b))
  return :: ShareableN a => Nondet (a --> m a)
  return = pure
  {-# MINIMAL (>>=) #-}

instance MonadND (ListND Nondet) where
  (>>=) = rtrnFunc $ \a -> rtrnFunc $ \f -> a P.>>= \case
    Nil       -> P.return Nil
    Cons x xs -> apply2 append (f `app` x) (apply2 (>>=) xs f)

-- | Lifted MonadFail type class
class MonadND m => MonadFailND m where
  fail :: ShareableN a => Nondet (StringND Nondet --> m a)

instance MonadFailND (ListND Nondet) where
  fail = rtrnFunc $ \_ -> P.return Nil

-- * Lifted Enum type class, instances and functions

-- | Lifted Enum type class
class EnumND a where
  succ :: Nondet (a --> a)
  succ = rtrnFunc $ \a ->
    toEnum `app` (apply2 (+) (liftE $ P.return 1) (fromEnum `app` a))
  pred :: Nondet (a --> a)
  pred = rtrnFunc $ \a ->
    toEnum `app` (apply2 (-) (liftE $ P.return 1) (fromEnum `app` a))

  toEnum   :: Nondet (IntND Nondet --> a)
  fromEnum :: Nondet (a --> IntND Nondet)

  enumFrom       :: Nondet (a             --> ListND Nondet a)
  enumFrom       = rtrnFunc $ \x1 ->
    apply2 map toEnum (enumFrom `app`
      (fromEnum `app` x1))

  enumFromThen   :: Nondet (a --> a       --> ListND Nondet a)
  enumFromThen   = rtrnFunc $ \x1 -> rtrnFunc $ \x2 ->
    apply2 map toEnum (apply2 enumFromThen
      (fromEnum `app` x1) (fromEnum `app` x2))

  enumFromTo     :: Nondet (a       --> a --> ListND Nondet a)
  enumFromTo     = rtrnFunc $ \x1 ->                   rtrnFunc $ \x3 ->
    apply2 map toEnum (apply2 enumFromTo
      (fromEnum `app` x1)                      (fromEnum `app` x3))

  enumFromThenTo :: Nondet (a --> a --> a --> ListND Nondet a)
  enumFromThenTo = rtrnFunc $ \x1 -> rtrnFunc $ \x2 -> rtrnFunc $ \x3 ->
    apply2 map toEnum (apply3 enumFromThenTo
      (fromEnum `app` x1) (fromEnum `app` x2) (fromEnum `app` x3))

instance EnumND (IntND Nondet) where
  succ = (+) `app` (liftE $ P.return 1)
  pred = (-) `app` (liftE $ P.return 1)

  toEnum   = id
  fromEnum = id

  enumFrom = rtrnFunc $ \x1 ->
    x1 P.>>= \(IntND v1) ->
    liftE (P.return (P.enumFrom v1))

  enumFromThen = rtrnFunc $ \x1 -> rtrnFunc $ \x2 ->
    x1 P.>>= \(IntND v1) -> x2 P.>>= \(IntND v2) ->
    liftE (P.return (P.enumFromThen v1 v2))

  enumFromTo = rtrnFunc $ \x1 -> rtrnFunc $ \x3 ->
    x1 P.>>= \(IntND v1) -> x3 P.>>= \(IntND v3) ->
    liftE (P.return (P.enumFromTo v1 v3))

  enumFromThenTo = rtrnFunc $ \x1 -> rtrnFunc $ \x2 -> rtrnFunc $ \x3 ->
    x1 P.>>= \(IntND v1) -> x2 P.>>= \(IntND v2) -> x3 P.>>= \(IntND v3) ->
    liftE (P.return (P.enumFromThenTo v1 v2 v3))

instance EnumND (IntegerND Nondet) where
  succ = (+) `app` (liftE $ P.return 1)
  pred = (-) `app` (liftE $ P.return 1)

  toEnum   = toInteger
  fromEnum = fromInteger

  enumFrom = rtrnFunc $ \x1 ->
    x1 P.>>= \(IntegerND v1) ->
    liftE (P.return (P.enumFrom v1))

  enumFromThen = rtrnFunc $ \x1 -> rtrnFunc $ \x2 ->
    x1 P.>>= \(IntegerND v1) -> x2 P.>>= \(IntegerND v2) ->
    liftE (P.return (P.enumFromThen v1 v2))

  enumFromTo = rtrnFunc $ \x1 -> rtrnFunc $ \x3 ->
    x1 P.>>= \(IntegerND v1) -> x3 P.>>= \(IntegerND v3) ->
    liftE (P.return (P.enumFromTo v1 v3))

  enumFromThenTo = rtrnFunc $ \x1 -> rtrnFunc $ \x2 -> rtrnFunc $ \x3 ->
    x1 P.>>= \(IntegerND v1) -> x2 P.>>= \(IntegerND v2) -> x3 P.>>= \(IntegerND v3) ->
    liftE (P.return (P.enumFromThenTo v1 v2 v3))

-- * Lifted Bounded type class, instances and functions

-- | Lifted Bounded type class
class BoundedND a where
  minBound :: Nondet a
  maxBound :: Nondet a

instance BoundedND (IntND Nondet) where
  minBound = liftE $ P.return P.minBound
  maxBound = liftE $ P.return P.maxBound

class IsStringND a where
  fromString :: Nondet (StringND Nondet --> a)

instance (a ~ CharND Nondet) => IsStringND (ListND Nondet a) where
  fromString = rtrnFunc $ \x -> x

{-

class Fractional a => Floating a where
  pi                  :: a
  exp, log, sqrt      :: a -> a
  (**), logBase       :: a -> a -> a
  sin, cos, tan       :: a -> a
  asin, acos, atan    :: a -> a
  sinh, cosh, tanh    :: a -> a
  asinh, acosh, atanh :: a -> a

  log1p               :: a -> a
  expm1               :: a -> a
  log1pexp            :: a -> a
  log1mexp            :: a -> a

  x ** y              =  exp (log x * y)
  logBase x y         =  log y / log x
  sqrt x              =  x ** 0.5
  tan  x              =  sin  x / cos  x
  tanh x              =  sinh x / cosh x

  log1p x = log (1 + x)
  expm1 x = exp x - 1
  log1pexp x = log1p (exp x)
  log1mexp x = log1p (negate (exp x))
-}
