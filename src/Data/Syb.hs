{- Temp module while syb is incompatible -}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Syb (module Data.Syb, Data, Typeable) where

import Data.Data

everywhere :: (forall a. Data a => a -> a)
           -> (forall a. Data a => a -> a)
everywhere f = go
  where
    go :: forall a. Data a => a -> a
    go = f . gmapT go

mkT :: ( Typeable a
       , Typeable b
       )
    => (b -> b)
    -> a
    -> a
mkT = extT id

-- | Extend a generic transformation by a type-specific case
extT :: ( Typeable a
        , Typeable b
        )
     => (a -> a)
     -> (b -> b)
     -> a
     -> a
extT def ext = unT ((T def) `ext0` (T ext))

-- | The type constructor for transformations
newtype T x = T { unT :: x -> x }

-- | Make a generic monadic transformation;
--   start from a type-specific case;
--   resort to return otherwise
--
mkM :: ( Monad m
       , Typeable a
       , Typeable b
       )
    => (b -> m b)
    -> a
    -> m a
mkM = extM return

-- | Extend a generic monadic transformation by a type-specific case
extM :: ( Monad m
        , Typeable a
        , Typeable b
        )
     => (a -> m a) -> (b -> m b) -> a -> m a
extM def ext = unM ((M def) `ext0` (M ext))


-- | The type constructor for transformations
newtype M m x = M { unM :: x -> m x }

-- | Flexible type extension
ext0 :: (Typeable a, Typeable b) => c a -> c b -> c a
ext0 def ext = maybe def id (gcast ext)

-- | Monadic variation on everywhere
everywhereM :: forall m. Monad m => GenericM m -> GenericM m
everywhereM f = go
  where
    go :: GenericM m
    go x = do
      x' <- gmapM go x
      f x'

-- | Generic monadic transformations,
--   i.e., take an \"a\" and compute an \"a\"
--
type GenericM m = forall a. Data a => a -> m a

type GenericQ r = forall a. Data a => a -> r

-- | Get a list of all entities that meet a predicate
listify :: Typeable r => (r -> Bool) -> GenericQ [r]
listify p = everything (++) ([] `mkQ` (\x -> if p x then [x] else []))

everything :: forall r. (r -> r -> r) -> GenericQ r -> GenericQ r
everything k f = go
  where
    go :: GenericQ r
    go x = foldl k (f x) (gmapQ go x)

mkQ :: ( Typeable a
       , Typeable b
       )
    => r
    -> (b -> r)
    -> a
    -> r
(r `mkQ` br) a = case cast a of
                        Just b  -> br b
                        Nothing -> r
