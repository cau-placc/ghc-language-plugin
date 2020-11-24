module Tests (tests) where

import Distribution.TestSuite
import System.Directory
import System.Process
import System.Exit

import SemanticTests

tests :: IO [Test]
tests = do
  path <- makeAbsolute "test-examples"
  setCurrentDirectory  path
  return [testGroup "Example Tests"
    [ Test (mkCompileTest Succeed    "Coin.hs")
    , Test (mkCompileTest Succeed    "Data.hs")
    , Test (mkCompileTest Succeed    "Import.hs")
    , Test (mkCompileTest ExpectFail "ImportHaskell.hs")
    , Test (mkCompileTest Succeed    "PatternMatching.hs")
    , Test (mkCompileTest Succeed    "Wrapper.hs")
    , Test (mkCompileTest Succeed    "Record.hs")
    , Test (mkCompileTest Succeed    "InstanceImport.hs")
    , Test (mkCompileTest Succeed    "PolyFailed.hs")
    , Test (mkCompileTest Succeed    "Typeclass.hs")
    , Test (mkCompileTest Succeed    "OverloadedStrings.hs")
    , Test (mkCompileTest Succeed    "MultiParamFlexible.hs")

    , Test (mkSemanticTest letPattern)
    , Test (mkSemanticTest unknownNat)
    , Test (mkSemanticTest guards)
    ]]

data Expected = Succeed | ExpectFail

mkCompileTest :: Expected -> FilePath -> TestInstance
mkCompileTest expect file = TestInstance
  { run = testGhcInvocation expect file
  , name = file
  , tags = []
  , options = []
  , setOption = \_ _ -> Left "Option not supported"
  }

testGhcInvocation :: Expected -> FilePath -> IO Progress
testGhcInvocation expect file = do
  process <- spawnProcess "ghc"
    ["-hidir out", "-odir out", "-fforce-recomp", "-dcore-lint", file]
  code <- waitForProcess process
  return $ case code of
    ExitSuccess   | Succeed    <- expect
      -> Finished Pass
    ExitSuccess   | ExpectFail <- expect
      -> Finished (Fail "Compilation succeeded, but was expected to fail")
    ExitFailure _ | ExpectFail <- expect
      -> Finished Pass
    ExitFailure _ | Succeed    <- expect
      -> Finished (Fail "Compilation failed unexpectedly")
