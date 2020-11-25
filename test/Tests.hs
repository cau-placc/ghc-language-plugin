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
    [ Test (mkCompileTest Succeed    "InstanceImport.hs")

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
