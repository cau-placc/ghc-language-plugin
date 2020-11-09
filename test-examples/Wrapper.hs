module Wrapper where

import Plugin.CurryPlugin.Encapsulation
import Coin

-- We can evaluate any nondeterministic computation
-- from within ordinary Haskell module.

-- Expected result: [True, False]
test :: [Bool]
test = eval DFS coin
