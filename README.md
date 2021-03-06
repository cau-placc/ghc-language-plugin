# Curry plugin for GHC

The goal of this project is to make prototypical implementation of a plugin
for the Glasgow Haskell Compiler (GHC),
such that the GHC can be used to compile Curry programs.

## Compatibility

This plugin only works with GHC 8.10.1 and cannot be used with other versions.

## Using the plugin
The plugin can be activated within a module by adding both
`{-# LANGUAGE NoImplicitPrelude #-} ` and
`{-# OPTIONS_GHC -fplugin Plugin.CurryPlugin #-}` to the top of the file.

A replacement Prelude can be imported from `import Plugin.CurryPlugin.Prelude`.
This brings a few basic functions, data types and type classes into scope, as well as
nondeterministic choice `(?) :: a -> a -> a` and `failed :: a`.

To capture all results of a nondeterministic computation, the user can import the computation in an ordinary Haskell module and use some of the following functions from `Plugin.CurryPlugin.Encapsulation` to get all results.

```haskell
data SearchMode = DFS | BFS

--   Examples:
--   >>> $(evalGeneric DFS 'someNullaryFunction)
--   >>> $(evalGeneric BFS 'someUnaryFunction  ) arg1
--   >>> (..)
evalGeneric :: SearchMode -> Name -> Q Exp

--   Examples:
--   >>> $(evalN 0) DFS someNullaryFunction
--   >>> $(evalN 1) BFS someUnaryFunction   arg1
--   >>> (..)
evalN :: Int -> Q Exp

--   Examples:
--   >>> eval DFS someNullaryFunction
eval  :: _ => SearchMode
      -> Nondet a -> [b]

--   Examples:
--   >>> eval1 BFS someUnaryFunction arg1
eval1 :: _ => SearchMode
      -> Nondet (a1 --> b1) -> a2 -> [b2]

--   Examples:
--   >>> eval2 BFS someBinaryFunction arg1 arg2
eval2 :: _ => SearchMode
      -> Nondet (a1 --> b1 --> c1) -> a2 -> b2 -> [c2]
```

## Using the plugin in a sandbox

A sandbox project is available to play around with in `sandbox/`. It can be loaded by executing `stack repl sandbox` from the root of the repository.

## Known Issues

 - Adding instances of derivable type classes to primitive types is not possible
 - Most Language extensions are unsupported and will crash at compilation or run-time, but some of the extensions might work.
 - Sharing in let-expressions does not work in some edge-cases
 - Using `:r` in GHCi only works on the second try
 - Type errors mention the nondeterministic versions of type constructors
 - HIE and HaskellLanguageServer do not work  
 - ~Stack outputs some decoding failures while compiling the project. This can be ignored safely.~ Fixed with stack version 2.3.3

## Debugging

In order see, when my plugin generates invalid code, use the GHC option `-dcore-lint`. This type checks the generated core-code and emits an error message when something went wrong. I am very interested in finding those issues.
This option can also be turned on via `{-# OPTIONS_GHC -dcore-lint #-}`
