open import ONNX.Syntax
open import ONNX.Semantics

module VNNLIB.Solver
  (onnxSyntax : NetworkTheorySyntax)
  (onnxSemantics : NetworkTheorySemantics onnxSyntax)
  where

open import Data.Maybe
open import Relation.Nullary.Decidable

open import VNNLIB.Syntax onnxSyntax
open import VNNLIB.Semantics onnxSemantics

-- A solver is a decision procedure that decides the
-- mathematical problem represented by the query
Solver : Set
Solver =
  (q : Query) →
  (N : NetworkImplementations (context q)) →
  Dec (⟦query⟧ q N)

-- A solver is an incomplete decision procedure that decides the
-- mathematical problem represented by the query
IncompleteSolver : Set
IncompleteSolver =
  (q : Query) →
  (N : NetworkImplementations (context q)) →
  Maybe (⟦query⟧ q N)
