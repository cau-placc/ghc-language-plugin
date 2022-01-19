{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Plugin.CurryPlugin.Main where

import Control.Monad (liftM2, replicateM)
import Plugin.CurryPlugin.Monad
import System.Random (getStdRandom, random)
import Prelude hiding (fail)

none :: None a -> a
none sig = case sig of

-- State

-- [operation | Get s :: s |]

newtype Get s a = Get (s -> a)
  deriving (Functor)

get :: (Get s :<: sig) => Free sig s
get = inject (Get return)

-- [operation | Put s :: s → () |]

data Put s a = Put s (() -> a)
  deriving (Functor)

put :: (Put s :<: sig) => s -> Free sig ()
put s = inject (Put s return)

comp :: (Get Integer :<: sig, Put Integer :<: sig) => Free sig Integer
comp = do
  x <- get
  put (x + 1)
  y <- get
  put (y + y)
  get

-- Closed handler for State

runState :: Free (Get s :+: Put s :+: None) a -> s -> (a, s)
runState = foldFree var (get \/ put \/ none)
  where
    var x s = (x, s)
    get (Get k) s = k s s
    put (Put s k) _ = k () s

example1 :: (Integer, Integer)
example1 = runState comp 1

evalState :: Free (Get s :+: Put s :+: None) a -> s -> a
evalState = foldFree var (get \/ put \/ none)
  where
    var x s = x
    get (Get k) s = k s s
    put (Put s k) _ = k () s

example2 :: Integer
example2 = evalState comp (1 :: Integer)

logState :: Free (Get s :+: Put s :+: None) a -> s -> (a, [s])
logState = foldFree var (get \/ put \/ none)
  where
    var x _ = (x, [])
    get (Get k) s = k s s
    put (Put s k) _ = let (x, ss) = k () s in (x, s : ss)

example3 :: (Integer, [Integer])
example3 = logState comp 1

-- Open handler for State

fwd :: (Functor sig) => sig (Free sig a) -> Free sig a
fwd = Op

fwdS :: (Functor sig) => sig (s -> Free sig a) -> s -> Free sig a
fwdS sig s = Op (fmap ($ s) sig)

fwdR :: (Functor sig1, Functor sig2) => sig2 (Free (sig1 :+: sig2) a) -> Free (sig1 :+: sig2) a
fwdR = Op . Inr

openState :: (Functor sig) => Free (Get s :+: Put s :+: sig) a -> s -> Free sig a
openState = foldFree var (get \/ put \/ fwdS)
  where
    var x s = return x
    get (Get k) s = k s s
    put (Put s k) _ = k () s

-- Example effect

data Choose1 a = Choose1 a a
  deriving (Functor)

newtype Choose2 a = Choose2 (Bool -> a)
  deriving (Functor)

data Choose3 a where
  Choose3 :: x -> x -> (x -> a) -> Choose3 a

instance Functor Choose3 where
  fmap f (Choose3 x1 x2 k) = Choose3 x1 x2 (f . k)

choose1 :: (Choose1 :<: sig) => Free sig a -> Free sig a -> Free sig a
choose1 fx fy = inject (Choose1 fx fy)

choose2 :: (Choose2 :<: sig) => Free sig Bool
choose2 = inject (Choose2 return)

choose3 :: (Choose3 :<: sig) => Free sig a -> Free sig a -> Free sig a
choose3 fx fy = inject (Choose3 fx fy id)

data Fail a = Fail
  deriving (Functor)

fail :: (Fail :<: sig) => Free sig a
fail = inject Fail

runND1 :: (Functor sig) => Free (Choose1 :+: Fail :+: sig) a -> Free sig [a]
runND1 = foldFree var (choose1 \/ fail \/ fwd)
  where
    var x = return [x]
    choose1 (Choose1 fx fy) = liftM2 (++) fx fy
    fail Fail = return []

runND2 :: (Functor sig) => Free (Choose2 :+: Fail :+: sig) a -> Free sig [a]
runND2 = foldFree var (choose2 \/ fail \/ fwd)
  where
    var x = return [x]
    choose2 (Choose2 k) = liftM2 (++) (k True) (k False)
    fail Fail = return []

runND3 :: (Functor sig) => Free (Choose3 :+: Fail :+: sig) a -> Free sig [a]
runND3 = foldFree var (choose3 \/ fail \/ fwd)
  where
    var x = return [x]
    choose3 (Choose3 fx fy k) = liftM2 (++) (k fx) (k fy)
    fail Fail = return []

newtype Random a = Random (Double -> a)
  deriving (Functor)

rand :: (Random :<: sig) => Free sig Double
rand = inject (Random return)

randomResult :: (Functor sig) => Free (Choose1 :+: sig) a -> Free (Random :+: sig) a
randomResult = foldFree var (choose \/ fwdR)
  where
    var = return
    choose (Choose1 fx fy) = do
      r <- rand
      if r < 0.5 then fx else fy

handleRandom :: Free (Random :+: None) a -> IO a
handleRandom = foldFree var (rand \/ none)
  where
    var = return
    rand (Random k) = do
      r <- getStdRandom random
      k r

maybeResult :: (Functor sig) => Free (Fail :+: sig) a -> Free sig (Maybe a)
maybeResult = foldFree var (fail \/ fwd)
  where
    var = return . Just
    fail Fail = return Nothing

sampleMaybe :: Free (Fail :+: (Choose1 :+: None)) a -> IO (Maybe a)
sampleMaybe = handleRandom . randomResult . maybeResult

-- Examples

data Toss = Heads | Tails
  deriving (Show)

drunkToss1 :: (Fail :<: sig, Choose1 :<: sig) => Free sig Toss
drunkToss1 = do
  caught <- choose1 (return True) (return False)
  if caught then choose1 (return Heads) (return Tails) else fail

drunkTosses1 :: (Fail :<: sig, Choose1 :<: sig) => Int -> Free sig [Toss]
drunkTosses1 n = replicateM n drunkToss1

example41 :: [[Toss]]
example41 = run (runND1 (drunkTosses1 2))

drunkToss2 :: (Fail :<: sig, Choose2 :<: sig) => Free sig Toss
drunkToss2 = do
  caught <- choose2
  if caught
    then do
      side <- choose2
      if side then return Heads else return Tails
    else fail

drunkTosses2 :: (Fail :<: sig, Choose2 :<: sig) => Int -> Free sig [Toss]
drunkTosses2 n = replicateM n drunkToss2

example42 :: [[Toss]]
example42 = run (runND2 (drunkTosses2 2))

drunkToss3 :: (Fail :<: sig, Choose3 :<: sig) => Free sig Toss
drunkToss3 = do
  caught <- choose3 (return True) (return False)
  if caught then choose3 (return Heads) (return Tails) else fail

drunkTosses3 :: (Fail :<: sig, Choose3 :<: sig) => Int -> Free sig [Toss]
drunkTosses3 n = replicateM n drunkToss3

example43 :: [[Toss]]
example43 = run (runND3 (drunkTosses3 2))

insert :: (Choose1 :<: sig, Fail :<: sig) => a -> [a] -> Free sig [a]
insert e [] = return [e]
insert e (y : ys) = choose1 (return (e : y : ys)) (fmap (y :) (insert e ys))

perm :: (Choose1 :<: sig, Fail :<: sig) => [a] -> Free sig [a]
perm [] = return []
perm (x : xs) = perm xs >>= insert x

example5 :: [[Int]]
example5 = run (runND1 (perm [1 .. 3]))

main :: IO ()
main = do
  print example1
  print example2
  print example3
  print example41
  print example42
  print example43
  print example5
