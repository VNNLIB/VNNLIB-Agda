# VNNLIB-Agda

This repository is the official Agda library for interacting with the [VNN-LIB standard](https://www.vnnlib.org/).
It includes:
- `ONNX.Syntax`: abstract interface for the syntax of ONNX
- `ONNX.Semantics`: abstract interface for the semantics of ONNX
- `ONNX.Parser`: very minimal abstract interface for parsing ONNX constants
- `VNNLIB.Syntax` - intrinsically-typed syntax for VNNLIB queries
- `VNNLIB.Parser` - ability to parse/type-check a string into VNNLIB queries.
- `VNNLIB.Semantics` - semantics for VNNLIB queries
- `VNNLIB.Theories` - orthogonal subsets of the query syntax
- `VNNLIB.Logics` - overall subsets of the query syntax
- `VNNLIB.Solver` - an interface for solvers of VNNLIB queries

## Known short-comings

* Does not yet cover:

  - Network equivalence statements
  - Logics and theories

## Version compatibility

| VNNLIB-Agda version | VNNLIB version |
| --- | --- |
| v1.0 | v2.0 |

## Requirements

- [Agda Standard Library](https://github.com/agda/agda-stdlib) v2.3
- [BNFC Parser](https://hackage.haskell.org/package/BNFC) v2.9.5

Later versions of these tools may work but are not tested.

## Setup

Agda does not yet have a good story for distributing libraries. Please follow the instructions for building from source in [CONTRIBUTING.md](https://github.com/VNNLIB/VNNLIB-Agda/blob/main/CONTRIBUTING.md).
