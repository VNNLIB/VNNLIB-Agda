# VNNLIB-Agda

This repository is a formalisation of the [VNN-LIB standard](https://github.com/VNNLIB/VNNLIB-Standard/).
It includes:
- Syntax for well-typed VNNLIB queries
- A parser and type-checker for VNNLIB queries
- Formal semantics for VNNLIB queries

## Requirements

- [Agda Standard Library](https://github.com/agda/agda-stdlib) (v2.3): utilized in the Agda formalization
- [VNNLIB-Standard](https://github.com/VNNLIB/VNNLIB-Standard) (v2.0): syntax: this is added as a submodule to this project.
- [BNFC Parser](https://hackage.haskell.org/package/BNFC) (v2.9.5): this is to generate the AST using the Agda backened from the syntax file.

Later versions of these tools may work but are not tested.

## Setup

1. Clone this repository.

2. Initialise the submodules to get the official VNN-LIB grammar from the VNN-LIB Standard repository
  ```bash
  git submodule update --init --recursive
  ```

3. Use BNFC to create the parser from the official VNN-LIB grammar.
  ```bash
  bnfc -d --agda VNNLIB-Standard/syntax.cf -o src -p VNNLIB
  ```