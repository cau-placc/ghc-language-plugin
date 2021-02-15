{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE TypeApplications          #-}
module Plugin.Effect.Transformers where

import qualified Data.IntMap         as IntMap
import qualified Data.Map.Strict     as Map
import           Data.Coerce
import           Unsafe.Coerce
import           Control.Monad
import           Control.Applicative
import           Control.Monad.State ( MonadState(..), gets, modify )
import           Control.Monad.Trans.Class

import Plugin.Effect.Classes

newtype LazyT m a = LazyT {
    fromLazyT :: forall r. (a -> Store -> m r) -> Store -> m r
  }

runLazyT :: Monad m => LazyT m a -> m a
runLazyT m = fromLazyT m (\a _ -> return a) emptyStore

mkShareNeedImpl :: forall n m a.
                   ( Sharing m
                   , Coercible (m a) (LazyT n a)
                   , Coercible (LazyT n (LazyT n a)) (m (m a)))
                => (a -> m a) -> m a -> m (m a)
mkShareNeedImpl sargs a =
  coerce (memo (coerce a >>= (coerce @(m a) @(LazyT n a)) . sargs))

newtype StrictT m a = StrictT {
    fromStrictT :: m a
  }

runStrictT :: Monad m => StrictT m a -> m a
runStrictT = fromStrictT

newtype NameT m a = NameT {
    fromNameT :: m a
  }

runNameT :: Monad m => NameT m a -> m a
runNameT = fromNameT

newtype TopSharingT m a = TopSharingT {
    fromTopSharingT :: forall r. (a -> TopStore -> m r) -> TopStore -> m r
  }

runTopSharingT :: Monad m => TopSharingT m a -> m a
runTopSharingT m = fromTopSharingT m (\a _ -> return a) emptyTopStore

instance MonadTrans LazyT where
  lift ma = LazyT $ \c s -> ma >>= \a -> c a s

instance MonadTrans StrictT where
  lift = StrictT

instance MonadTrans NameT where
  lift = NameT

instance MonadTrans TopSharingT where
  lift ma = TopSharingT $ \c s -> ma >>= \a -> c a s

deriving instance Functor (LazyT m)

instance Functor m => Functor (StrictT m) where
  fmap f a = StrictT $ fmap f $ fromStrictT a

instance Functor m => Functor (NameT m) where
  fmap f a = NameT $ fmap f $ fromNameT a

deriving instance Functor (TopSharingT m)

instance Applicative (LazyT m) where
  pure x = LazyT (\c -> c x)
  (<*>)  = ap

instance Applicative m => Applicative (StrictT m) where
  pure = StrictT . pure
  mf <*> ma = StrictT $ fromStrictT mf <*> fromStrictT ma

instance Applicative m => Applicative (NameT m) where
  pure = NameT . pure
  mf <*> ma = NameT $ fromNameT mf <*> fromNameT ma

instance Applicative (TopSharingT m) where
  pure x = TopSharingT (\c -> c x)
  (<*>)  = ap

instance Monad (LazyT m) where
  a >>= k = LazyT (\c s -> fromLazyT a (\x -> fromLazyT (k x) c) s)

instance Monad m => Monad (StrictT m) where
  ma >>= f = StrictT $ fromStrictT ma >>= fromStrictT . f

instance Monad m => Monad (NameT m) where
  ma >>= f = NameT $ fromNameT ma >>= fromNameT . f

instance Monad (TopSharingT m) where
  a >>= k =
    TopSharingT (\c s -> fromTopSharingT a (\x -> fromTopSharingT (k x) c) s)

instance Alternative m => Alternative (LazyT m) where
  empty = LazyT (\_ _ -> empty)
  m1 <|> m2 = LazyT (\c s -> fromLazyT m1 c s <|> fromLazyT m2 c s)

instance MonadPlus m => MonadPlus (LazyT m) where
  mzero = lift mzero
  m1 `mplus` m2 = LazyT (\c s -> fromLazyT m1 c s `mplus` fromLazyT m2 c s)


-- instance Alternative m => Alternative (LazyT m) where
--   empty = LazyT (\c s -> empty >>= c s)
--   m1 <|> m2 = LazyT (\c s1 -> fromLazyT m1
--                     (\x s2 -> fromLazyT m2
--                     (\y s3 -> )))

instance Sharing (LazyT m) where
  type ShareConstraints (LazyT m) a = Shareable (LazyT m) a
  share a = memo (a >>= shareArgs share)

instance Monad m => Sharing (StrictT m) where
  type ShareConstraints (StrictT m) a = ()
  share a = a >>= return . return

instance Monad m => Sharing (NameT m) where
  type ShareConstraints (NameT m) a = ()
  share = return

instance SharingTop m => SharingTop (LazyT m) where
  shareTopLevel k v = LazyT (\c s -> shareTopLevel k (fromLazyT v c s))

instance SharingTop m => SharingTop (StrictT m) where
  shareTopLevel k ma = StrictT $ shareTopLevel k $ fromStrictT ma

instance SharingTop m => SharingTop (NameT m) where
  shareTopLevel k ma = NameT $ shareTopLevel k $ fromNameT ma

instance SharingTop (TopSharingT m) where
  shareTopLevel = readOrExecuteTop

readOrExecuteTop :: (Int, String) -> TopSharingT m a -> TopSharingT m a
readOrExecuteTop k v = do
  entry <- gets (Map.lookup k . unwrapTopStore)
  case entry of
    Just val -> return (typed val)
    _        -> do
      val <- v
      modify (TopStore . Map.insert k (untyped val) . unwrapTopStore)
      return val

-- | A data type to label and store shared nondeterministic values
-- on an untyped heap.
data Store = Store
  { nextLabel :: !Int
  , heap :: !(IntMap.IntMap Untyped)
  }

instance MonadState Store (LazyT m) where
  get   = LazyT (\c s -> c s  s)
  put s = LazyT (\c _ -> c () s)

-- | An empty storage.
emptyStore :: Store
emptyStore = Store 0 IntMap.empty

-- | Get a new fresh label.
freshLabel :: MonadState Store m => m Int
freshLabel = do
  s <- get
  put (s {nextLabel = nextLabel s + 1})
  return (nextLabel s)

-- | Look up the vaule for a given label in the store.
lookupValue :: MonadState Store m => Int -> m (Maybe a)
lookupValue k = gets (fmap typed . IntMap.lookup k . heap)

-- | Store a given value for later.
storeValue :: MonadState Store m => Int -> a -> m ()
storeValue k v =
  modify (\s -> s { heap = IntMap.insert k (Untyped v) (heap s) })

{-# INLINE memo #-}
-- | Memorize a nondeterministic value for explicit sharing.
memo :: LazyT m a -> LazyT m (LazyT m a)
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

-- | Wrap a typed value in an untyped container.
data Untyped = forall a. Untyped a

-- | Wrap a typed value in an untyped container.
untyped :: a -> Untyped
untyped = Untyped

-- | Extract a typed value from an untyped container.
typed :: Untyped -> a
typed (Untyped x) = unsafeCoerce x

data TopStore = TopStore {
    unwrapTopStore :: Map.Map (Int, String) Untyped
  }

instance MonadState TopStore (TopSharingT m) where
  get   = TopSharingT (\c s -> c s  s)
  put s = TopSharingT (\c _ -> c () s)

emptyTopStore :: TopStore
emptyTopStore = TopStore Map.empty
