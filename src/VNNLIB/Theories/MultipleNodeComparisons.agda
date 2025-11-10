open import ONNX.Syntax

module VNNLIB.Theories.MultipleNodeComparisons
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.Unit.Base using (⊤)
open import Data.List using (List)
open import Data.List.NonEmpty using (length)
open import Data.Product.Base using (_×_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax

private
  variable
    Γ Γ₁ Γ₂ : NetworkContext
    
----------------
-- Theory set --
----------------

data MultipleNodeComparisons : Set where
  MIO : MultipleNodeComparisons
  SIO : MultipleNodeComparisons

---------
-- SIO --
---------  

record _ConnectedTo_Via_
  (output : OutputDeclaration)
  (input : InputDeclaration)
  (assertions : List (Assertion Γ)) : Set where
  field
    equalTypes : outputType output ≡ inputType input

SingleNodeComparison : List (Assertion Γ) → AssertionPredicate
SingleNodeComparison assertions = {!!}

-- A query lives in the SIO theory 
SingleNodeComparisonsTheory : Theory
SingleNodeComparisonsTheory q =
  AllAssertions (SingleNodeComparison (assertions q)) q

---------
-- MIO --
---------

-- Every query lives in the MIO theory
MultipleNodeComparisonsTheory : Theory
MultipleNodeComparisonsTheory = U

--------------------
-- Interpretation --
--------------------

instance
  MultipleNodeComparisonsInterpretation : Interpretation MultipleNodeComparisons
  MultipleNodeComparisonsInterpretation = record
    { interpretation = λ
      { SIO → SingleNodeComparisonsTheory
      ; MIO → MultipleNodeComparisonsTheory
      }
    }
