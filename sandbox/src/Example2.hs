{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin -ddump-tc -dsuppress-coercions -fprint-typechecker-elaboration -fplugin-opt Plugin.CurryPlugin:dump-deriving-errs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns    #-}
module Example2 where

import Example

use :: Boor
use = test T