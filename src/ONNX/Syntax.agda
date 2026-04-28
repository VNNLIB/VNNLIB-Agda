module ONNX.Syntax where

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.NonEmpty.Base
open import Data.List.NonEmpty.Relation.Binary.Pointwise using (Pointwise)
open import Data.String.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Level
open import Data.Tensor using (TensorShape)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- A signature for a tensor
record TensorType (Types : Set) : Set where
  constructor tensorType
  field
    tensorType : Types
    tensorDims : TensorShape

TensorShapesMatch : {Types₁ Types₂ : Set} → TensorType Types₁ → TensorType Types₂ → Set
TensorShapesMatch δ₁ δ₂ = tensorDims δ₁ ≡ tensorDims δ₂
  where open TensorType

InputTypes : (Types : Set) → Set
InputTypes Types = List⁺ (TensorType Types)

HiddenNodeTypes : (Types : Set) → Set
HiddenNodeTypes Types = List (TensorType Types)

OutputTypes : (Types : Set) → Set
OutputTypes Types = List⁺ (TensorType Types)

-- A signature for a network
record NetworkType (Types : Set) : Set where
  constructor networkType
  field
    inputs : InputTypes Types
    outputs : OutputTypes Types

NetworkShapesMatch : {Types₁ Types₂ : Set} → NetworkType Types₁ → NetworkType Types₂ → Set
NetworkShapesMatch (networkType inputs₁ outputs₁) (networkType inputs₂ outputs₂) =
  Pointwise TensorShapesMatch inputs₁ inputs₂ ×
  Pointwise TensorShapesMatch outputs₁ outputs₂

NetworkTypesMatch : {Types : Set} → NetworkType Types → NetworkType Types → Set
NetworkTypesMatch γ₁ γ₂ = γ₁ ≡ γ₂

-- An implementation of the syntax for models of neural networks necessary to define
-- the syntax of VNN-LIB.
record NetworkTheorySyntax : Set₁ where
  field
    -- The set of numeric element types allowed by the network theory
    ElementType : Set

    -- The internal representation of tensors in the network theory
    TheoryTensor : TensorType ElementType → Set

    -- The internal representation of networks in the network theory
    Model : NetworkType ElementType → Set

    -- The set of allowable names for the output tensors of nodes inside of networks
    NodeOutputName : Set
    
    -- A judgement that a node contains an output with a given name
    NodeOutput : ∀ {γ} → Model γ → NodeOutputName → TensorType ElementType → Set 

    -- A function that maps a model to a list of its outputs
    modelOutputs : ∀ {γ} (m : Model γ) → All⁺ (λ δ → ∃ λ u → NodeOutput m u δ) (NetworkType.outputs γ)

    -- A judgement that two models are isomorphic
    _↭[_]_ : ∀ {γ₁} {γ₂} → Model γ₁ → NetworkShapesMatch γ₁ γ₂ → Model γ₂ → Set

  -- A judgement that two models are equal (i.e. the actual same file)
  _≡[_]_ : ∀ {γ₁} {γ₂} → Model γ₁ → NetworkTypesMatch γ₁ γ₂ → Model γ₂ → Set
  N₁ ≡[ refl ] N₂ = N₁ ≡ N₂
