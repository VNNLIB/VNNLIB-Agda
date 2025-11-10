
open import ONNX.Syntax

module ONNX.Semantics where

open import Data.Bool.Base
open import Data.List.Relation.Unary.All using (All)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Level

open import Data.Tensor

-- The type of unary tensor operations
TensorOp1 : Set → Set
TensorOp1 τ = ∀ {shape} → Tensor τ shape → Tensor τ shape

-- The type of binary tensor operations
TensorOp2 : Set → Set
TensorOp2 τ = ∀ {shape} → Tensor τ shape → Tensor τ shape → Tensor τ shape

-- The type of tensor comparisons
TensorComp : Set → Set
TensorComp τ = ∀ {shape} → Tensor τ shape → Tensor τ shape → Bool

TensorSemantics : ∀ {Types : Set} → (Types → Set) → TensorType Types → Set
TensorSemantics sem (tensorType τ shape) = Tensor (sem τ) shape

InputsSemantics : ∀ {Types : Set} → (Types → Set) → InputTypes Types → Set
InputsSemantics sem tensorTypes = All⁺ (TensorSemantics sem) tensorTypes

OutputsSemantics : ∀ {Types : Set} → (Types → Set) → OutputTypes Types → Set
OutputsSemantics sem tensorTypes = All⁺ (TensorSemantics sem) tensorTypes

-- The semantics of networks
NetworkSemantics : ∀ {Types : Set} → (Types → Set) → NetworkType Types → Set
NetworkSemantics sem (networkType inputTypes outputTypes) =
  InputsSemantics sem inputTypes → OutputsSemantics sem outputTypes

-- An implementation of the subset of the semantics of ONNX necessary to define
-- the semantics of VNN-LIB.
record NetworkTheorySemantics (syn : NetworkTheorySyntax) : Set₁ where
  open NetworkTheorySyntax syn
  field
    -- The interpretation of network types
    ⟦theoryType⟧    : TheoryType → Set
    -- The interpretation of network tensors
    ⟦theoryTensor⟧  : ∀ {τ} → TheoryTensor τ → TensorSemantics ⟦theoryType⟧ τ
    -- The interpretation of network networks
    ⟦theoryNetwork⟧ : ∀ {τ} → TheoryNetwork τ → NetworkSemantics ⟦theoryType⟧ τ
    
    -- The interpretation of the basic ONNX tensor operations at each type
    ⟦≤⟧   : ∀ {τ} → TensorComp (⟦theoryType⟧ τ) 
    ⟦<⟧   : ∀ {τ} → TensorComp (⟦theoryType⟧ τ) 
    ⟦≥⟧   : ∀ {τ} → TensorComp (⟦theoryType⟧ τ) 
    ⟦>⟧   : ∀ {τ} → TensorComp (⟦theoryType⟧ τ) 
    ⟦=⟧   : ∀ {τ} → TensorComp (⟦theoryType⟧ τ) 
    ⟦≠⟧   : ∀ {τ} → TensorComp (⟦theoryType⟧ τ) 
    ⟦neg⟧ : ∀ {τ} → TensorOp1  (⟦theoryType⟧ τ)
    ⟦add⟧ : ∀ {τ} → TensorOp2  (⟦theoryType⟧ τ)
    ⟦mul⟧ : ∀ {τ} → TensorOp2  (⟦theoryType⟧ τ)
