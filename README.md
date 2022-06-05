# Language Plugin

The goal of this project is to make prototypical implementation of a plugin
for the Glasgow Haskell Compiler (GHC),
such that the GHC can be used to compile programs that contain an implicit monadic effect.

## Compatibility

This plugin only works with GHC 9.2 and cannot be used with other versions.

## Examples
The plugin has been used to create two example languages.
- One Curry-Style functional logic language [curry-ghc-language-plugin](https://github.com/cau-placc/curry-ghc-language-plugin)
- One strict language with IO side effects (similar to ML) [ml-ghc-language-plugin](https://github.com/cau-placc/ml-ghc-language-plugin)

A fork of this has also been used to create a plugin for automatic function Inversion in Haskell. 
Details are in [this paper](https://dl.acm.org/doi/10.1145/3471874.3472982) and the project can be found at (https://github.com/cau-placc/inversion-plugin).
