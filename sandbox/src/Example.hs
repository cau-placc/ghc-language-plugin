{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# OPTIONS_GHC -dsuppress-coercions -dsuppress-module-prefixes -fprint-typechecker-elaboration #-}
--{-# OPTIONS_GHC -ddump-tc #-}
--{-# OPTIONS_GHC -fplugin-opt Plugin.CurryPlugin:dump-original #-}
{-# LANGUAGE DataKinds #-}
module Example where

data Boor = T | F

no :: Boor -> Boor
no T = F
no F = T

i :: a -> a
i x = x

{-# ANN test1 (closed @'[Fail, Choose1]) #-}
test1 :: Boor
test1 = i T

test2 :: Boor
test2 = no T
