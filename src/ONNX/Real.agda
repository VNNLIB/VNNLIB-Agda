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
open import Data.List.NonEmpty.Relation.Unary.All renaming (All to All⁺)
open import Data.List.NonEmpty.Relation.Unary.AllUtils as All

open NetworkTheorySyntax theorySyntax
open TensorType using (tensorDims)

-------------------
-- Preliminaries --
-------------------

_SameShapeAs_ : ∀ {Types₁ Types₂ : Set} → TensorType Types₁ → TensorType Types₂ → Set
δ₁ SameShapeAs δ₂ = tensorDims δ₁ ≡ tensorDims δ₂

_SameShapesAs_ : ∀ {Types₁ Types₂ : Set} → List⁺ (TensorType Types₁) → List⁺ (TensorType Types₂) → Set
xs SameShapesAs ys = Pointwise _SameShapeAs_ xs ys

record _SameNetworkShapeAs_ {Types₁ Types₂ : Set} (τ₁ : NetworkType Types₁) (τ₂ : NetworkType Types₂) : Set where
  constructor sameNetworkShape
  open NetworkType
  field
    inputsRelated  : (inputs τ₁) SameShapesAs (inputs τ₂)
    outputsRelated : (outputs τ₁) SameShapesAs (outputs τ₂)
  
------------
-- Syntax --
------------

-- There is only one syntactic type `real` 
record RealElementType : Set where
  constructor real

-- Tensors in the syntax are Agda tensors
RealTheoryTensor : TensorType RealElementType → Set
RealTheoryTensor type = Tensor ℝ (tensorDims type)

-- Networks are just a network from the parent theory that have input and output
-- tensors that have the required shape (although the element types will necessarily differ!)
record RealModel (networkType : NetworkType RealElementType) : Set where
  constructor realModel
  field
    {runtimeNetworkType} : NetworkType ElementType
    runtimeNetwork : Model runtimeNetworkType
    sameShape : runtimeNetworkType SameNetworkShapeAs networkType

-- Likewise nodes are just nodes from the parent theory that match the required shape
-- (although the element types will necessarily differ!)
record RealNode {γ} (network : RealModel γ) (nodeType : TensorType RealElementType) : Set where
  constructor realNode
  field
    {runtimeNodeType} : TensorType ElementType
    runtimeNode : Node (RealModel.runtimeNetwork network) runtimeNodeType
    sameShape : runtimeNodeType SameShapeAs nodeType

realInputNodes : ∀ {γ} (n : RealModel γ) → All⁺ (RealNode n) (NetworkType.inputs γ)
realInputNodes (realModel runtimeNetwork (sameNetworkShape inputsSameShape _)) =
  All.zipWith realNode (inputNodes runtimeNetwork) inputsSameShape

realOutputNodes : ∀ {γ} (n : RealModel γ) → All⁺ (RealNode n) (NetworkType.outputs γ)
realOutputNodes (realModel runtimeNetwork (sameNetworkShape _ outputsSameShape)) =
  All.zipWith realNode (outputNodes runtimeNetwork) outputsSameShape

RealNodeHasOutput : ∀ {γ} {n : RealModel γ} {δ} → RealNode n δ → NodeOutputName → Set
RealNodeHasOutput (realNode runtimeNode sameNodeShape) = NodeHasOutput runtimeNode

realSyntax : NetworkTheorySyntax
realSyntax = record
  { ElementType = RealElementType
  ; TheoryTensor = RealTheoryTensor
  ; Model = RealModel
  ; NodeOutputName = NodeOutputName
  ; Node = RealNode
  ; inputNodes = realInputNodes
  ; outputNodes = realOutputNodes
  ; NodeHasOutput = RealNodeHasOutput
  }

---------------
-- Semantics --
---------------

open NetworkTheorySemantics theorySemantics

-- The `real` type is interpreted as `ℝ`
⟦realElementType⟧ : RealElementType → Set
⟦realElementType⟧ real = ℝ

-- This type encodes the idea that given any syntactic network in the theory we
-- can deduce the semantics of the network as if it operated over the real numbers.
RealNetworkSemantics : Set
RealNetworkSemantics =
  ∀ {γ₁ γ₂} →
  (n : Model γ₁) →
  γ₁ SameNetworkShapeAs γ₂ →
  InputSemantics ⟦realElementType⟧ γ₂ →
  ∀ {δ₁ δ₂} →
  Node n δ₁ →
  δ₁ SameShapeAs δ₂ →
  TensorSemantics ⟦realElementType⟧ δ₂

⟦realTheoryTensor⟧ : ∀ {τ} → RealTheoryTensor τ → TensorSemantics ⟦realElementType⟧ τ
⟦realTheoryTensor⟧ tensor = tensor

-- Given some way of interpreting the syntactic networks as networks over reals,
-- we simply run the real interpretation.
⟦realModel⟧ : RealNetworkSemantics → ∀ {γ} (n : RealModel γ) → InputSemantics ⟦realElementType⟧ γ → ∀ {δ} → RealNode n δ → TensorSemantics ⟦realElementType⟧ δ
⟦realModel⟧ ⟦realNetwork⟧ (realModel runtimeNetwork sameShape) realInputs (realNode runtimeNode sameNodeShape) =
  ⟦realNetwork⟧ runtimeNetwork sameShape realInputs runtimeNode sameNodeShape
  
realSemantics : RealNetworkSemantics → NetworkTheorySemantics realSyntax
realSemantics realNetworkSemantics = record
  { ⟦elementType⟧    = ⟦realElementType⟧
  ; ⟦theoryTensor⟧  = ⟦realTheoryTensor⟧
  ; ⟦model⟧ = ⟦realModel⟧ realNetworkSemantics
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
