{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE RankNTypes #-}
module Example where

import Plugin.CurryPlugin.Prelude

newtype I a = I a

bind :: I a -> (a -> I b) -> I b
bind (I a) f = f a

applyBoth :: I (I (forall c. I c -> I c) -> I (I (I a, I b) -> I (I a, I b)))
-- Nondet ((forall a. a)
applyBoth = I (\f -> I (\t -> f `bind` (\f' -> t `bind` (\(a, b) -> I (f' a, f' b)))))
