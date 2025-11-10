open import ONNX.Syntax

module VNNLIB.Theories.Definition
  (networkSyntax : NetworkTheorySyntax)
  where

open import VNNLIB.Syntax networkSyntax

-- A theory is a predicate over a query
Theory : Set₁
Theory = Query → Set

-- An interpretation of a theory set is a mapping of each
-- element in the set to a theory
record Interpretation (TheorySet : Set) : Set₁ where
  field
    interpretation : TheorySet → Theory

-- Use instance arguments to map any theory in a theory set to
-- its interpretation
_∈_ :
  {TheorySet : Set}
  {{_ : Interpretation TheorySet}} →
  Query →
  TheorySet →
  Set
_∈_ {{interp}} q theory = Interpretation.interpretation interp theory q
