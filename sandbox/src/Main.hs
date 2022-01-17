{-# LANGUAGE TemplateHaskell #-}
module Main where

import Example
import Plugin.CurryPlugin.Encapsulation

main :: IO ()
main = putStrLn $ "There are " ++ show (length res) ++
                  " permutations of a list of length " ++ show n
  where
    n = 3
    res = $(evalGeneric DFS 'permutations) [(1::Int)..n]
