open import ONNX.Syntax
open import ONNX.Semantics

module ONNX.Real
  (theorySyntax : NetworkTheorySyntax)
  (theorySemantics : NetworkTheorySemantics theorySyntax)
  where

open import Data.Product.Base
open import Function.Base
open import Data.List.NonEmpty as List⁺
open import Data.List.NonEmpty.Relation.Binary.Pointwise
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Real
open import Data.Tensor

open NetworkTheorySyntax theorySyntax
open TensorType using (tensorDims)

-------------------
-- Preliminaries --
-------------------

_SameShapesAs_ : ∀ {Types₁ Types₂ : Set} → List⁺ (TensorType Types₁) → List⁺ (TensorType Types₂) → Set
xs SameShapesAs ys = Pointwise (λ τ₁ τ₂ → tensorDims τ₁ ≡ tensorDims τ₂) xs ys

record _SameNetworkShapeAs_ {Types₁ Types₂ : Set} (τ₁ : NetworkType Types₁) (τ₂ : NetworkType Types₂) : Set where
  open NetworkType
  field
    inputsRelated  : (inputs τ₁) SameShapesAs (inputs τ₂)
    outputsRelated : (outputs τ₁) SameShapesAs (outputs τ₂)
  
------------
-- Syntax --
------------

-- There is only one syntactic type `real` 
record RealTheoryType : Set where
  constructor real

-- Tensors in the syntax are Agda tensors
RealTheoryTensor : TensorType RealTheoryType → Set
RealTheoryTensor type = Tensor ℝ (tensorDims type)

-- Networks are just a network from the parent theory that have input and output
-- tensors that have the required shape (although the types will necessarily differ!)
record RealTheoryNetwork (networkType : NetworkType RealTheoryType) : Set where
  constructor realTheoryNetwork
  field
    {runtimeNetworkType} : NetworkType TheoryType
    runtimeNetwork : TheoryNetwork runtimeNetworkType
    sameShape : runtimeNetworkType SameNetworkShapeAs networkType

realSyntax : NetworkTheorySyntax
realSyntax = record
  { TheoryType = RealTheoryType
  ; TheoryTensor = RealTheoryTensor
  ; TheoryNetwork = RealTheoryNetwork
  }

---------------
-- Semantics --
---------------

open NetworkTheorySemantics theorySemantics

-- The `real` type is interpreted as `ℝ`
⟦realTheoryType⟧ : RealTheoryType → Set
⟦realTheoryType⟧ _ = ℝ

-- This type encodes the idea that given any syntactic network in the theory we
-- can deduce the semantics of the network as if it operated over the real numbers.
RealNetworkSemantics : Set
RealNetworkSemantics =
  ∀ {τ₁ τ₂} →
  TheoryNetwork τ₁ →
  τ₁ SameNetworkShapeAs τ₂ →
  NetworkSemantics ⟦realTheoryType⟧ τ₂

⟦realTheoryTensor⟧ : ∀ {τ} → RealTheoryTensor τ → TensorSemantics ⟦realTheoryType⟧ τ
⟦realTheoryTensor⟧ tensor = tensor

-- Given some way of interpreting the syntactic networks as networks over reals,
-- we simply run the real interpretation.
⟦realTheoryNetwork⟧ : RealNetworkSemantics → ∀ {τ} → RealTheoryNetwork τ → NetworkSemantics ⟦realTheoryType⟧ τ
⟦realTheoryNetwork⟧ ⟦realNetwork⟧ (realTheoryNetwork runtimeNetwork sameShape) realInputs = do
  ⟦realNetwork⟧ runtimeNetwork sameShape realInputs
  
realSemantics : RealNetworkSemantics → NetworkTheorySemantics realSyntax
realSemantics realNetworkSemantics = record
  { ⟦theoryType⟧    = ⟦realTheoryType⟧
  ; ⟦theoryTensor⟧  = ⟦realTheoryTensor⟧
  ; ⟦theoryNetwork⟧ = ⟦realTheoryNetwork⟧ realNetworkSemantics
  ; ⟦≤⟧ = comparePointwise _≤ᵇ_
  ; ⟦<⟧ = comparePointwise _<ᵇ_
  ; ⟦≥⟧ = comparePointwise _≥ᵇ_
  ; ⟦>⟧ = comparePointwise _>ᵇ_
  ; ⟦=⟧ = comparePointwise _=ᵇ_
  ; ⟦≠⟧ = comparePointwise _≠ᵇ_
  ; ⟦neg⟧ = mapTensor (0ℝ -_)
  ; ⟦add⟧ = zipTensor _+_
  ; ⟦mul⟧ = zipTensor _*_
  }
