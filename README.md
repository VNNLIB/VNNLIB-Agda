# VNNLIB-Agda

This repository is the official Agda library for interacting with the [VNN-LIB standard](https://www.vnnlib.org/).
It includes:
- `ONNX.Syntax`: abstract interface for the syntax of ONNX
- `ONNX.Semantics`: abstract interface for the semantics of ONNX
- `ONNX.Parser`: very minimal abstract interface for parsing ONNX constants
- `VNNLIB.Syntax`: intrinsically-typed syntax for VNNLIB queries
- `VNNLIB.Parser`: ability to parse/type-check a string into VNNLIB queries.
- `VNNLIB.Semantics`: semantics for VNNLIB queries
- `VNNLIB.Theories`: orthogonal subsets of the query syntax
- `VNNLIB.Logics`: overall subsets of the query syntax
- `VNNLIB.Solver`: an interface for solvers of VNNLIB queries
- `VNNLIB.Example`: some simple examples of how to use the library.

## Known short-comings

* Does not yet cover all the logics and theories in VNNLIB 2.0.

## Version compatibility

| VNNLIB-Agda version | VNNLIB version |
| --- | --- |
| v1.0 | v2.0 |

## Requirements

- [Agda Standard Library](https://github.com/agda/agda-stdlib) v2.3
- [BNFC Parser](https://hackage.haskell.org/package/BNFC) v2.9.5

Later versions of these tools may work but are not tested.

## Setup

Agda does not yet have a good story for distributing libraries. Please follow the following instructions:

1. Install the Agda standard library

2. Clone this repository with submodules and navigate into it:
   ```bash
   git clone --recurse-submodules https://github.com/VNNLIB/VNNLIB-Agda.git
   cd VNNLIB-Agda
   ```
3. Generate the BNFC parser from the official VNNLIB BNFC grammar:
   ```bash
   bnfc -d --agda VNNLIB-Standard/grammar.cf -o src -p VNNLIB
   ```

## Getting started with the library

See the `VNNLIB.Examples` file for:

1. An example of how to represent a simple VNNLIB query natively in Agda

2. How to prove the soundness of a simple, example compiler pass.