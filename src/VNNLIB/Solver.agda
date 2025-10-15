open import ONNX.Syntax
open import ONNX.Semantics

module VNNLIB.Solver
  (onnxSyntax : ONNXSyntax)
  (onnxSemantics : ONNXSemantics onnxSyntax)
  where

open import Data.Maybe
open import Relation.Nullary.Decidable

open import VNNLIB.Syntax onnxSyntax
open import VNNLIB.Semantics onnxSyntax onnxSemantics

Solver : Set
Solver = (q : Query) (N : ONNXNetworks (context q)) → Dec (⟦query⟧ q N)

IncompleteSolver : Set
IncompleteSolver = (q : Query) (N : ONNXNetworks (context q)) → Maybe (⟦query⟧ q N)
