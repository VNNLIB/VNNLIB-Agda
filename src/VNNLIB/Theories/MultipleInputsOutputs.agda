open import ONNX.Syntax

module VNNLIB.Theories.MultipleInputsOutputs
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.Unit.Base using (⊤)
open import Data.List.NonEmpty using (length)
open import Data.Product.Base using (_×_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax

----------------
-- Theory set --
----------------

data MultipleInputsOutputs : Set where
  MIO : MultipleInputsOutputs
  SIO : MultipleInputsOutputs

---------
-- SIO --
---------  

SingleInputOutput : NetworkPredicate
SingleInputOutput network =
  length (inputDeclarations network)  ≡ 1 ×
  length (outputDeclarations network) ≡ 1

-- A query lives in the SIO theory 
SingleInputsOutputsTheory : Theory
SingleInputsOutputsTheory (query networks _) =
  AllNetworks SingleInputOutput networks

---------
-- MIO --
---------

-- Every query lives in the MIO theory
MultipleInputsOutputsTheory : Theory
MultipleInputsOutputsTheory = U

--------------------
-- Interpretation --
--------------------

instance
  MultipleInputsOutputsInterpretation : Interpretation MultipleInputsOutputs
  MultipleInputsOutputsInterpretation = record
    { interpretation = λ
      { SIO → SingleInputsOutputsTheory
      ; MIO → SingleInputsOutputsTheory
      }
    }
