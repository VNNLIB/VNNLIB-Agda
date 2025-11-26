
open import ONNX.Syntax

module ONNX.Semantics where

open import Data.Bool.Base
open import Data.List.Base using (List; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.List.NonEmpty.Base using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Level

open import Data.Tensor

module _ {ElementType : Set} (⟦ElementType⟧ : ElementType → Set) where

  TensorSemantics : TensorType ElementType → Set
  TensorSemantics (tensorType τ shape) = Tensor (⟦ElementType⟧ τ) shape

  InputSemantics : NetworkType ElementType → Set
  InputSemantics (networkType inputTypes _) = All⁺ TensorSemantics inputTypes
  
  -- The type of unary tensor operations
  TensorOp1 : TensorType ElementType → Set
  TensorOp1 δ = TensorSemantics δ → TensorSemantics δ

  -- The type of binary tensor operations
  TensorOp2 : TensorType ElementType → Set
  TensorOp2 δ = TensorSemantics δ → TensorSemantics δ → TensorSemantics δ

  -- The type of tensor comparisons
  TensorComp : TensorType ElementType → Set
  TensorComp δ = TensorSemantics δ → TensorSemantics δ → Bool

  NetworkSemantics : List⁺ (TensorType ElementType) → TensorType ElementType → Set
  NetworkSemantics inputTypes outputType = All⁺ TensorSemantics inputTypes → TensorSemantics outputType


-- An implementation of the subset of the semantics of ONNX necessary to define
-- the semantics of VNN-LIB.
record NetworkTheorySemantics (syn : NetworkTheorySyntax) : Set₁ where
  open NetworkTheorySyntax syn
  
  field
    -- The interpretation of network types
    ⟦elementType⟧ : ElementType → Set
    
    -- The interpretation of network tensors
    ⟦theoryTensor⟧  : ∀ {τ} → TheoryTensor τ → TensorSemantics ⟦elementType⟧ τ
    
    -- The interpretation of a network allows us to evaluate the network at any node
    ⟦model⟧ : ∀ {γ} (n : Model γ) → InputSemantics ⟦elementType⟧ γ → ∀ {δ u} → NodeOutput n u δ → TensorSemantics ⟦elementType⟧ δ
    
    -- The interpretation of the basic ONNX tensor operations at each type
    ⟦≤⟧   : ∀ {δ} → TensorComp ⟦elementType⟧ δ 
    ⟦<⟧   : ∀ {δ} → TensorComp ⟦elementType⟧ δ 
    ⟦≥⟧   : ∀ {δ} → TensorComp ⟦elementType⟧ δ 
    ⟦>⟧   : ∀ {δ} → TensorComp ⟦elementType⟧ δ 
    ⟦=⟧   : ∀ {δ} → TensorComp ⟦elementType⟧ δ 
    ⟦≠⟧   : ∀ {δ} → TensorComp ⟦elementType⟧ δ 
    ⟦neg⟧ : ∀ {δ} → TensorOp1  ⟦elementType⟧ δ
    ⟦add⟧ : ∀ {δ} → TensorOp2  ⟦elementType⟧ δ
    ⟦mul⟧ : ∀ {δ} → TensorOp2  ⟦elementType⟧ δ
