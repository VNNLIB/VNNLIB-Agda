# VNNLIB-Agda
⚠️ Work-in-Progress: Agda parser for VNNLIB.

This repository includes the following for Agda formalisation for the [VNN-LIB standard](https://github.com/VNNLIB/VNNLIB-Standard/):
- Formal syntax and semantics of a query
- Formalisation of a well-scoped & well-typed query including a parser

## Additional Software Requirements
- [Agda Standard Library](https://github.com/agda/agda-stdlib): utilized in the Agda formalization
- [VNNLIB-Standard](https://github.com/VNNLIB/VNNLIB-Standard) syntax: this is added as a submodule to this project.
- [BNFC Parser](https://hackage.haskell.org/package/BNFC): this is to generate the AST using the Agda backened from the syntax file.

## Generate the BNFC Agda parser
```bash
bnfc -d -m --agda VNNLIB-Standard/syntax.cf -o src
```