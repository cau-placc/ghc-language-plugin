{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
module SemanticTests where

import Distribution.TestSuite
import Control.Concurrent

import Plugin.CurryPlugin.Encapsulation

import qualified Tests.Guards     as Test
import qualified Tests.UnknownNat as Test
import qualified Tests.LetPattern as Test

data SemanticTestDescr = forall a. (Eq a, Show a) => TestDescr
  {  testExpr   :: a
  ,  testResult :: a
  ,  testName   :: String
  }

unknownNat :: SemanticTestDescr
unknownNat = TestDescr
  { testExpr   = take 1 (eval DFS Test.unknownNat)
  , testResult = [1]
  , testName   = "unknownNat"
  }

guards :: SemanticTestDescr
guards = TestDescr
  { testExpr   = take 1 (eval2 DFS Test.take 3 [(1 :: Int)..10])
  , testResult = [[1,2,3]]
  , testName   = "take"
  }

letPattern :: SemanticTestDescr
letPattern = TestDescr
  { testExpr   = not (null (eval DFS Test.letPattern))
  , testResult = True
  , testName   = "letPattern"
  }

mkSemanticTest :: SemanticTestDescr -> TestInstance
mkSemanticTest (TestDescr e expected nm) = TestInstance
  { run = do
      res <- timeout 2000000 (return (e `seq` e))
      return $ case res of
        Just r | r == expected
                 -> Finished Pass
               | otherwise
                 -> Finished (Fail ("Expected: " ++ show expected ++
                                    ", but the result is: " ++ show r))
        Nothing  -> Finished (Fail "Computation timed out")
  , name = nm
  , tags = ["Semantic"]
  , options = []
  , setOption = \_ _ -> Left "Option not supported"
  }

timeout :: Int -> IO a -> IO (Maybe a)
timeout usec action = compete
  [fmap Just action, threadDelay usec >> return Nothing]

compete :: [IO a] -> IO a
compete actions = do
  mvar <- newEmptyMVar
  tids <- mapM (\action -> forkIO $ action >>= putMVar mvar) actions
  result <- takeMVar mvar
  mapM_ killThread tids
  return result
