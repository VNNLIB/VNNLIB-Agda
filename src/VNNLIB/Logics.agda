open import ONNX.Syntax

module VNNLIB.Logics
  (networkSyntax : NetworkTheorySyntax)
  where

open import Relation.Unary using (_∩_)

open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories networkSyntax

----------------
-- Definition --
----------------

record Logic : Set where
  field
    mioTheory : MultipleInputsOutputs

-------------------
-- Intepretation --
-------------------

interpretation : Logic → Query → Set
interpretation logic =
  _∈ mioTheory
  -- ∩ _∈ hiddenTheory
  where open Logic logic

instance
  LogicInterpration : Interpretation Logic
  LogicInterpration = record
    { interpretation = interpretation
    }
