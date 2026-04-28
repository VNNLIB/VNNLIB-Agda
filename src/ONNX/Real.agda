open import ONNX.Syntax
open import ONNX.Semantics

module ONNX.Real
  (theorySyntax : NetworkTheorySyntax)
  (theorySemantics : NetworkTheorySemantics theorySyntax)
  where

open import Data.Product.Base
open import Function.Base
open import Data.List.NonEmpty as List⁺
open import Data.List.NonEmpty.Relation.Binary.Pointwise as Pointwise
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Data.Real
open import Data.Tensor
open import Data.List.NonEmpty.Relation.Unary.All renaming (All to All⁺)
open import Data.List.NonEmpty.Relation.Unary.AllUtils as All

open NetworkTheorySyntax theorySyntax
open TensorType using (tensorDims)

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
    sameShape : NetworkShapesMatch runtimeNetworkType networkType

RealNodeOutputName : Set
RealNodeOutputName = NodeOutputName

-- Likewise nodes are just nodes from the parent theory that match the required shape
-- (although the element types will necessarily differ!)
record RealNodeOutput {γ} (network : RealModel γ) (name : RealNodeOutputName) (nodeType : TensorType RealElementType) : Set where
  constructor realNodeOutput
  field
    {runtimeNodeType} : TensorType ElementType
    runtimeNode : NodeOutput (RealModel.runtimeNetwork network) name runtimeNodeType
    sameShape : TensorShapesMatch runtimeNodeType nodeType

realModelOutputs : ∀ {γ} (n : RealModel γ) → All⁺ (λ δ → ∃ λ u → RealNodeOutput n u δ) (NetworkType.outputs γ)
realModelOutputs (realModel runtimeNetwork (_ , outputsSameShape)) =
  All.zipWith (λ {(u , z) eq → (u , realNodeOutput z eq)}) (modelOutputs runtimeNetwork) outputsSameShape

_↭R[_]_ : ∀ {γ₁ γ₂} → RealModel γ₁ → NetworkShapesMatch γ₁ γ₂ → RealModel γ₂ → Set
M ↭R[ s ] N = runtimeNetwork M ↭[ transN (sameShape M) (transN s (symN (sameShape N))) ] runtimeNetwork N
  where
  open RealModel

  transN : ∀ {t₁ t₂ t₃} {γ₁ : NetworkType t₁} {γ₂ : NetworkType t₂} {γ₃ : NetworkType t₃} → NetworkShapesMatch γ₁ γ₂ → NetworkShapesMatch γ₂ γ₃ → NetworkShapesMatch γ₁ γ₃
  transN (in₁ , out₁) (in₂ , out₂) = Pointwise.transitive trans in₁ in₂ , Pointwise.transitive trans out₁ out₂

  symN : ∀ {t₁ t₂} {γ₁ : NetworkType t₁} {γ₂ : NetworkType t₂} → NetworkShapesMatch γ₁ γ₂ → NetworkShapesMatch γ₂ γ₁
  symN (in₁ , out₁) = Pointwise.symmetric sym in₁ , Pointwise.symmetric sym out₁

  
realSyntax : NetworkTheorySyntax
realSyntax = record
  { ElementType    = RealElementType
  ; TheoryTensor   = RealTheoryTensor
  ; Model          = RealModel
  ; NodeOutputName = RealNodeOutputName
  ; NodeOutput     = RealNodeOutput
  ; modelOutputs   = realModelOutputs
  ; _↭[_]_        = _↭R[_]_
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
  NetworkShapesMatch γ₁ γ₂ →
  InputSemantics ⟦realElementType⟧ γ₂ →
  ∀ {δ₁ δ₂ u} →
  NodeOutput n u δ₁ →
  TensorShapesMatch δ₁ δ₂ →
  TensorSemantics ⟦realElementType⟧ δ₂

⟦realTheoryTensor⟧ : ∀ {τ} → RealTheoryTensor τ → TensorSemantics ⟦realElementType⟧ τ
⟦realTheoryTensor⟧ tensor = tensor

-- Given some way of interpreting the syntactic networks as networks over reals,
-- we simply run the real interpretation.
⟦realModel⟧ : RealNetworkSemantics → ∀ {γ} (n : RealModel γ) → InputSemantics ⟦realElementType⟧ γ → ∀ {δ u} → RealNodeOutput n u δ → TensorSemantics ⟦realElementType⟧ δ
⟦realModel⟧ ⟦realNetwork⟧ (realModel runtimeNetwork sameShape) realInputs (realNodeOutput runtimeNode sameNodeShape) =
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
