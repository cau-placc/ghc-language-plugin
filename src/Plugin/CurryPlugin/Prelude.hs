{-# LANGUAGE NoImplicitPrelude              #-}
{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns    #-}
{-|
Module      : Plugin.CurryPlugin.ForeignExport
Description : Prelude for the Curry-Plugin
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module is the replacement Prelude to be used with the Curry-Plugin.
Most of these definitions are from Haskell's default Prelude and not from me.
-}
module Plugin.CurryPlugin.Prelude
 ( module Plugin.CurryPlugin.ForeignExport
 , module Plugin.CurryPlugin.Prelude
 ) where

import Plugin.CurryPlugin.ForeignExport

------------------------------------------
-- Bool
------------------------------------------
infixr 3 &&
infixr 2 ||

(&&) :: Bool -> Bool -> Bool
True  && True = True
_     && _    = False

(||) :: Bool -> Bool -> Bool
True  || _ = True
False || x = x

not :: Bool -> Bool
not True  = False
not False = True

otherwise :: Bool
otherwise = True

------------------------------------------
-- Maybe
------------------------------------------

data Maybe a = Nothing
             | Just a
  deriving Eq

instance Functor Maybe where
  fmap _ Nothing  = Nothing
  fmap f (Just a) = Just (f a)

instance Applicative Maybe where
  pure = Just
  Just f <*> Just a = Just (f a)
  _      <*> _      = Nothing

instance Alternative Maybe where
  empty = Nothing
  Just x  <|> _ = Just x
  Nothing <|> y = y

instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just a  >>= f = f a

instance MonadFail Maybe where
  fail _ = Nothing

maybe :: b -> (a -> b) -> Maybe a -> b
maybe _ f (Just a) = f a
maybe b _ Nothing  = b

------------------------------------------
-- Either
------------------------------------------

data Either a b = Left a | Right b
  deriving Eq

instance Functor (Either a) where
  fmap _ (Left  a) = Left a
  fmap f (Right b) = Right (f b)

instance Applicative (Either a) where
  pure = Right
  Left  e <*> _ = Left e
  Right f <*> y = fmap f y

instance Monad (Either a) where
  Left e  >>= _ = Left e
  Right a >>= f = f a

------------------------------------------
-- Tuples
------------------------------------------

fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, y) = y

curry :: ((a, b) -> c) -> a -> b -> c
curry f a b = f (a, b)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

------------------------------------------
-- Numeric functions
------------------------------------------

subtract :: Num a => a -> a -> a
subtract x y = y - x

------------------------------------------
-- Misc. functions
------------------------------------------

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

flip :: (a -> b -> c) -> b -> a -> c
flip f b a = f a b

($) :: (a -> b) -> a -> b
($) f x = f x

until :: (a -> Bool) -> (a -> a) -> a -> a
until p f = go
  where
    go x | p x          = x
         | otherwise    = go (f x)

asTypeOf :: a -> a -> a
asTypeOf x _ = x

------------------------------------------
-- List operations
------------------------------------------

map :: (a -> b) -> [a] -> [b]
map = fmap

infixr 5 ++

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys

filter :: (a -> Bool) -> [a] -> [a]
filter _ []     = []
filter p (x:xs)
  | p x         = x : filter p xs
  | otherwise   = filter p xs

head :: [a] -> a
head (x:_) = x

last :: [a] -> a
last [x]    = x
last (_:xs) = last xs

tail :: [a] -> [a]
tail (_:xs) = xs

init :: [a] -> [a]
init (x:xs) = init' x xs
  where
    init' _ []     = []
    init' y (z:zs) = y : init' z zs

infixl 9 !!
(!!) :: [a] -> Int -> a
(x:xs) !! n =
  if n == 0
    then x
    else xs !! (n - 1)

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ b []     = b
foldr f b (x:xs) = x `f` foldr f b xs

foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 f (x:xs) = foldr f x xs

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ b []     = b
foldl f b (x:xs) = foldl f b xs `f` x

foldl1 :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs) = foldl f x xs

null :: [a] -> Bool
null [] = True
null _  = False

length :: [a] -> Int
length = foldl (\c _ -> c + 1) 0

reverse :: [a] -> [a]
reverse = reverse' []
  where
    reverse' acc []     = acc
    reverse' acc (x:xs) = reverse' (x:acc) xs

and :: [Bool] -> Bool
and = foldr (&&) True

or :: [Bool] -> Bool
or = foldr (||) False

any :: (a -> Bool) -> [a] -> Bool
any p = foldr (\a b -> p a || b) False

all :: (a -> Bool) -> [a] -> Bool
all p = foldr (\a b -> p a && b) True

concat :: [[a]] -> [a]
concat = foldr (++) []

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = foldr (\a b -> f a ++ b) []

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

-- a recursive definition is better than a cyclic one, as long as sharing
-- in cyclic structures is unsupported
repeat :: a -> [a]
repeat x = x : repeat x

-- same as in repeat
cycle :: [a] -> [a]
cycle xs = xs ++ cycle xs

elem :: Eq a => a -> [a] -> Bool
elem a = any (a==)

notElem :: Eq a => a -> [a] -> Bool
notElem a = all (a/=)

zip :: [a] -> [b] -> [(a, b)]
zip []     _      = []
zip _      []     = []
zip (a:as) (b:bs) = (a, b) : zip as bs

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith _ []     _      = []
zipWith _ _      []     = []
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs

unzip :: [(a, b)] -> ([a], [b])
unzip []            = ([], [])
unzip ((a, b) : xs) = (a:as, b:bs)
  where
    (as, bs) = unzip xs
