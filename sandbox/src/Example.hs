{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin -ddump-tc -dsuppress-coercions -fprint-typechecker-elaboration -fplugin-opt Plugin.CurryPlugin:dump-deriving-errs #-}
module Example where

data Boor = T | F

test :: Boor -> Boor
test T = F
test F = T
test _ = failed


-- permutations :: [a] -> [a]
-- permutations []     = []
-- permutations (x:xs) = insert x (permutations xs)
--   where
--     insert e []     = [e]
--     insert e (y:ys) = (e:y:ys) ? (y : insert e ys)

-- test :: Int
-- test = 1 + 2
-- -- test = 3

-- test2 :: Int -> Int
-- test2 x = double 2 + x
-- -- test2 = 4 + x

-- double :: Int -> Int
-- double x = x * 2
-- -- double x = x * 2

-- test3 :: Bool
-- test3 = f (True ? False)
-- -- test3 = False ? True
--   where
--     f True = False
--     f False = True