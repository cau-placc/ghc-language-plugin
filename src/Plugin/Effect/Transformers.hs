{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE DisambiguateRecordFields  #-}
{-# LANGUAGE DuplicateRecordFields     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE UndecidableInstances      #-}
module Plugin.Effect.Transformers where

import qualified Data.IntMap         as IntMap
import qualified Data.Map.Strict     as Map
import           Data.Coerce
import           Data.Kind
import           Unsafe.Coerce
import           Control.Monad
import           Control.Applicative
import           Control.Monad.State ( MonadState(..) )
import           Control.Monad.Trans.Class

import Plugin.Effect.Classes

newtype LazyT (n :: Type -> Type) m a = LazyT {
    fromLazyT :: forall r. (a -> Store -> m r) -> Store -> m r
  }

runLazyT :: Monad m => LazyT n m a -> m a
runLazyT m = fromLazyT m (\a _ -> return a) emptyStore

newtype StrictT (n :: Type -> Type) m a = StrictT {
    fromStrictT :: m a
  }

runStrictT :: Monad m => StrictT n m a -> m a
runStrictT = fromStrictT

newtype NameT (n :: Type -> Type) m a = NameT {
    fromNameT :: m a
  }

runNameT :: Monad m => NameT n m a -> m a
runNameT = fromNameT

newtype TopSharingT (n :: Type -> Type) m a = TopSharingT {
    fromTopSharingT :: forall r. (a -> TopStore -> m r) -> TopStore -> m r
  }

runTopSharingT :: Monad m => TopSharingT n m a -> m a
runTopSharingT m = fromTopSharingT m (\a _ -> return a) emptyTopStore

newtype TopSharingAndLazyT (n :: Type -> Type) m a = TopSharingAndLazyT {
    fromTopSharingAndLazyT :: forall r. (a -> Store -> TopStore -> m r)
                                           -> Store -> TopStore -> m r
  }

runTopSharingAndLazyT :: Monad m => TopSharingAndLazyT n m a -> m a
runTopSharingAndLazyT m =
  fromTopSharingAndLazyT m (\a _ _ -> return a) emptyStore emptyTopStore

instance MonadTrans (LazyT n) where
  lift ma = LazyT $ \c s -> ma >>= \a -> c a s

instance MonadTrans (StrictT n) where
  lift = StrictT

instance MonadTrans (NameT n) where
  lift = NameT

instance MonadTrans (TopSharingT n) where
  lift ma = TopSharingT $ \c s -> ma >>= \a -> c a s

instance MonadTrans (TopSharingAndLazyT n) where
  lift ma = TopSharingAndLazyT $ \c s t -> ma >>= \a -> c a s t

deriving instance Functor (LazyT n m)

instance Functor m => Functor (StrictT n m) where
  fmap f a = StrictT $ fmap f $ fromStrictT a

instance Functor m => Functor (NameT n m) where
  fmap f a = NameT $ fmap f $ fromNameT a

deriving instance Functor (TopSharingT n m)

deriving instance Functor (TopSharingAndLazyT n m)

instance Applicative (LazyT n m) where
  pure x = LazyT (\c -> c x)
  (<*>)  = ap

instance Applicative m => Applicative (StrictT n m) where
  pure = StrictT . pure
  mf <*> ma = StrictT $ fromStrictT mf <*> fromStrictT ma

instance Applicative m => Applicative (NameT n m) where
  pure = NameT . pure
  mf <*> ma = NameT $ fromNameT mf <*> fromNameT ma

instance Applicative (TopSharingT n m) where
  pure x = TopSharingT (\c -> c x)
  (<*>)  = ap

instance Applicative (TopSharingAndLazyT n m) where
  pure x = TopSharingAndLazyT (\c -> c x)
  (<*>)  = ap

instance Monad (LazyT n m) where
  a >>= k = LazyT (\c s -> fromLazyT a (\x -> fromLazyT (k x) c) s)

instance Monad m => Monad (StrictT n m) where
  ma >>= f = StrictT $ fromStrictT ma >>= fromStrictT . f

instance Monad m => Monad (NameT n m) where
  ma >>= f = NameT $ fromNameT ma >>= fromNameT . f

instance Monad (TopSharingT n m) where
  a >>= k = TopSharingT $ \c s ->
    fromTopSharingT a (\x -> fromTopSharingT (k x) c) s

instance Monad (TopSharingAndLazyT n m) where
  a >>= k = TopSharingAndLazyT $ \c s t ->
    fromTopSharingAndLazyT a (\x -> fromTopSharingAndLazyT (k x) c) s t

instance Alternative m => Alternative (LazyT n m) where
  empty = LazyT (\_ _ -> empty)
  m1 <|> m2 = LazyT (\c s -> fromLazyT m1 c s <|> fromLazyT m2 c s)

instance Alternative m => Alternative (StrictT n m) where
  empty = StrictT empty
  m1 <|> m2 = StrictT $ fromStrictT m1 <|> fromStrictT m2

instance Alternative m => Alternative (NameT n m) where
  empty = NameT empty
  m1 <|> m2 = NameT $ fromNameT m1 <|> fromNameT m2

instance Alternative m => Alternative (TopSharingAndLazyT n m) where
  empty = TopSharingAndLazyT (\_ _ _ -> empty)
  m1 <|> m2 = TopSharingAndLazyT $ \c s t ->
    fromTopSharingAndLazyT m1 c s t <|> fromTopSharingAndLazyT m2 c s t

instance MonadPlus m => MonadPlus (LazyT n m) where
  mzero = lift mzero
  m1 `mplus` m2 = LazyT (\c s -> fromLazyT m1 c s `mplus` fromLazyT m2 c s)

instance MonadPlus m => MonadPlus (StrictT n m) where
  mzero = lift mzero
  m1 `mplus` m2 = StrictT $ fromStrictT m1 `mplus` fromStrictT m2

instance MonadPlus m => MonadPlus (NameT n m) where
  mzero = lift mzero
  m1 `mplus` m2 = NameT $ fromNameT m1 `mplus` fromNameT m2

instance MonadPlus m => MonadPlus (TopSharingAndLazyT n m) where
  mzero = lift mzero
  m1 `mplus` m2 = TopSharingAndLazyT $ \c s t ->
    fromTopSharingAndLazyT m1 c s t `mplus` fromTopSharingAndLazyT m2 c s t

instance ( forall a. Coercible (n a) (LazyT n m a)
         , forall a. Coercible (LazyT n m a) (n a)
         , Sharing n ) => Sharing (LazyT n m) where
  type ShareConstraints (LazyT n m) a = Shareable n a
  share :: forall a. Shareable n a => LazyT n m a -> LazyT n m (LazyT n m a)
  share a = memo (coerce (coerce @(LazyT n m a) @(n a) a >>= shareArgs))

instance Monad m => Sharing (StrictT n m) where
  type ShareConstraints (StrictT n m) a = ()
  share a = a >>= return . return

instance Monad m => Sharing (NameT n m) where
  type ShareConstraints (NameT n m) a = ()
  share = return

instance ( forall a. Coercible (n a) (TopSharingAndLazyT n m a)
         , forall a. Coercible (TopSharingAndLazyT n m a) (n a)
         , Sharing n ) => Sharing (TopSharingAndLazyT n m) where
  type ShareConstraints (TopSharingAndLazyT n m) a = Shareable n a
  share :: forall a. Shareable n a => TopSharingAndLazyT n m a
        -> TopSharingAndLazyT n m (TopSharingAndLazyT n m a)
  share a = memoBoth (coerce (coerce @(TopSharingAndLazyT n m a) @(n a) a
                                >>= shareArgs))

instance SharingTop m => SharingTop (StrictT n m) where
  type ShareTopConstraints (StrictT n m) a = ShareTopConstraints m a
  shareTopLevel k a = (coerce :: m a -> StrictT n m a)
    (shareTopLevel k ((coerce :: StrictT n m a -> m a) a))

instance SharingTop m => SharingTop (NameT n m) where
  type ShareTopConstraints (NameT n m) a = ShareTopConstraints m a
  shareTopLevel k a = (coerce :: m a -> NameT n m a)
    (shareTopLevel k ((coerce :: NameT n m a -> m a) a))

instance ( forall a. Coercible (n a) (TopSharingT n m a)
         , forall a. Coercible (TopSharingT n m a) (n a)
         , Sharing n) => SharingTop (TopSharingT n m) where
  type ShareTopConstraints (TopSharingT n m) a = ShareConstraints n a
  shareTopLevel :: forall a. ShareConstraints n a
                => (Int, String) -> TopSharingT n m a -> TopSharingT n m a
  shareTopLevel k v = do
    (TopStore _ h) <- get
    case Map.lookup k h of
      Just val -> coerce @(n a) @(TopSharingT n m a) (typed val)
      _        -> do
        val <- coerce (share (coerce @(TopSharingT n m a) @(n a) v))
        (TopStore i _) <- get
        put (TopStore i (Map.insert k (untyped val) h))
        coerce @(n a) @(TopSharingT n m a) val

instance Sharing (TopSharingAndLazyT n m) =>
         SharingTop (TopSharingAndLazyT n m) where
  type ShareTopConstraints (TopSharingAndLazyT n m) a =
    ShareConstraints (TopSharingAndLazyT n m) a
  shareTopLevel k v = do
    (_, TopStore _ h) <- get
    case Map.lookup k h of
      Just val -> typed val
      _        -> do
        val <- share v
        (s, TopStore i _) <- get
        put (s, TopStore i (Map.insert k (untyped val) h))
        val

-- | Wrap a typed value in an untyped container.
data Untyped = forall a. Untyped a

-- | Wrap a typed value in an untyped container.
untyped :: a -> Untyped
untyped = Untyped

-- | Extract a typed value from an untyped container.
typed :: Untyped -> a
typed (Untyped x) = unsafeCoerce x

-- | A data type to label and store shared nondeterministic values
-- on an untyped heap.
data Store = Store
  { nextLabel :: !Int
  , heap :: !(IntMap.IntMap Untyped)
  }

instance MonadState Store (LazyT n m) where
  get   = LazyT (\c s -> c s  s)
  put s = LazyT (\c _ -> c () s)

-- | An empty storage.
emptyStore :: Store
emptyStore = Store 0 IntMap.empty

{-# INLINE memo #-}
-- | Memorize a value for explicit sharing.
memo :: forall n m a. LazyT n m a -> LazyT n m (LazyT n m a)
memo a =
  LazyT
    (\c1 (Store key heap1) ->
      c1
        (LazyT
          (\c2 s@(Store _ heap2) ->
            case IntMap.lookup key heap2 of
              Just x -> c2 (typed x) s
              Nothing ->
                fromLazyT
                  a
                  (\x (Store other heap3) ->
                    c2 x (Store other (IntMap.insert key (Untyped x) heap3)))
                  s))
        (Store (succ key) heap1))

{-# INLINE memoBoth #-}
-- | Memorize a value for explicit sharing.
memoBoth :: TopSharingAndLazyT n m a
         -> TopSharingAndLazyT n m (TopSharingAndLazyT n m a)
memoBoth a =
  TopSharingAndLazyT
    (\c1 (Store key heap1) t1 ->
      c1
        (TopSharingAndLazyT
          (\c2 s@(Store _ heap2) t2 ->
            case IntMap.lookup key heap2 of
              Just x -> c2 (typed x) s t2
              Nothing ->
                fromTopSharingAndLazyT
                  a
                  (\x (Store other heap3) ->
                    c2 x (Store other (IntMap.insert key (Untyped x) heap3)))
                  s t2))
        (Store (succ key) heap1) t1)

data TopStore = TopStore {
    nextLabel :: Int,
    topHeap   :: Map.Map (Int, String) Untyped
  }

instance MonadState TopStore (TopSharingT n m) where
  get   = TopSharingT (\c s -> c s  s)
  put s = TopSharingT (\c _ -> c () s)

emptyTopStore :: TopStore
emptyTopStore = TopStore 0 Map.empty

memoTop :: (Int, String) -> TopSharingT n m a
        -> TopSharingT n m (TopSharingT n m a)
memoTop (i, str) a =
  TopSharingT
    (\c1 (TopStore offset heap1) -> let key = (i + offset, str) in
      c1
        (TopSharingT
          (\c2 s@(TopStore _ heap2) ->
            case Map.lookup key heap2 of
              Just x  -> c2 (typed x) s
              Nothing ->
                fromTopSharingT
                  a
                  (\x (TopStore other heap3) ->
                    c2 x (TopStore other (Map.insert key (Untyped x) heap3)))
                  s))
        (TopStore (succ offset) heap1))

memoTopBoth :: (Int, String) -> TopSharingAndLazyT n m a
            -> TopSharingAndLazyT n m (TopSharingAndLazyT n m a)
memoTopBoth (i, str) a =
  TopSharingAndLazyT
    (\c1 s1 (TopStore offset heap1) -> let key = (i + offset, str) in
      c1
        (TopSharingAndLazyT
          (\c2 s2 t@(TopStore _ heap2) ->
            case Map.lookup key heap2 of
              Just x  -> c2 (typed x) s2 t
              Nothing ->
                fromTopSharingAndLazyT
                  a
                  (\x s3 (TopStore other heap3) ->
                    c2 x s3 (TopStore other (Map.insert key (Untyped x) heap3)))
                  s2 t))
        s1 (TopStore (succ offset) heap1))

instance MonadState (Store, TopStore) (TopSharingAndLazyT n m) where
  get        = TopSharingAndLazyT (\c s t -> c (s, t) s t)
  put (s, t) = TopSharingAndLazyT (\c _ _ -> c ()     s t)
