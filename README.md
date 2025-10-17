# VNNLIB-Agda
⚠️ Work-in-Progress: Agda parser for VNNLIB.

This repository includes the following for Agda formalisation for the [VNN-LIB standard](https://github.com/VNNLIB/VNNLIB-Standard/):
- Formal syntax and semantics of a query
- Formalisation of a well-scoped & well-typed query including a parser

## Additional Software Requirements

Later versions may work but are not tested.

- [Agda Standard Library](https://github.com/agda/agda-stdlib) (v2.3): utilized in the Agda formalization
- [VNNLIB-Standard](https://github.com/VNNLIB/VNNLIB-Standard) (v2.0): syntax: this is added as a submodule to this project.
- [BNFC Parser](https://hackage.haskell.org/package/BNFC) (v2.9.5): this is to generate the AST using the Agda backened from the syntax file.

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
