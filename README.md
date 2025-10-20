# VNNLIB-Agda

This repository is the official Agda library for interacting with the [VNN-LIB standard](https://www.vnnlib.org/).
It includes:
- Syntax for well-typed VNNLIB queries
- A parser and type-checker for VNNLIB queries
- Formal semantics for VNNLIB queries

## Version compatability

| VNNLIB-Agda version | VNNLIB version |
| --- | --- |
| v1.0 | v2.0 |

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