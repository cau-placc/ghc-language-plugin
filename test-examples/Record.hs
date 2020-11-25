{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}
{-# LANGUAGE NoImplicitPrelude              #-}
{-# LANGUAGE RecordWildCards                #-}
{-# LANGUAGE NamedFieldPuns                 #-}
module Record where

import Plugin.CurryPlugin.Prelude

-- Record syntax is fully supported:

-- Record datatypes
data Rec = Rec { fromRec :: Int }
         | NoRec

-- Record patterns
test1 :: Rec -> Int
test1 Rec { fromRec = x } = x
test1 NoRec               = 0

-- Record patterns with RecordWildcards
test2 :: Rec -> Int
test2 Rec { .. } = fromRec
test2 NoRec      = 0

-- Record patterns with NamedFieldPuns
test2 :: Rec -> Int
test2 Rec { fromRec } = fromRec
test2 NoRec      = 0

-- Record constructors
test3 :: Rec
test3 = Rec { fromRec = 1 }

-- Record updates
test4 :: Rec
test4 = test3 { fromRec = 2 }
