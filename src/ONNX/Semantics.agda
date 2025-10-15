
open import ONNX.Syntax

module ONNX.Semantics where

open import Data.Bool.Base
open import Data.DependentList
open import Level

open import tensor

-- The type of unary tensor operations
TensorOp1 : Set → Set → Set
TensorOp1 τ₁ τ₂ = ∀ {shape} → Tensor τ₁ shape → Tensor τ₂ shape

-- The type of binary tensor operations
TensorOp2 : Set → Set → Set → Set
TensorOp2 τ₁ τ₂ τ₃ = ∀ {shape} → Tensor τ₁ shape → Tensor τ₂ shape → Tensor τ₃ shape

TensorSemantics : ∀ {Types : Set} → (Types → Set) → TensorSignature Types → Set
TensorSemantics sem (tensorSig τ shape) = Tensor (sem τ) shape

InputsSemantics : ∀ {Types : Set} → (Types → Set) → InputsSignature Types → Set
InputsSemantics sem tensorSigs = DepList (TensorSemantics sem) tensorSigs

OutputsSemantics : ∀ {Types : Set} → (Types → Set) → InputsSignature Types → Set
OutputsSemantics sem tensorSigs = DepList (TensorSemantics sem) tensorSigs

-- The semantics of networks
NetworkSemantics : ∀ {Types : Set} → (Types → Set) → NetworkSignature Types → Set
NetworkSemantics sem (networkSig inputs outputs) =
  InputsSemantics sem inputs → OutputsSemantics sem outputs

-- An implementation of the subset of the semantics of ONNX necessary to define
-- the semantics of VNN-LIB.
record ONNXSemantics (syn : ONNXSyntax) : Set₁ where
  open ONNXSyntax syn
  field
    -- The interpretation of ONNX types
    ⟦_⟧type    : ONNXType → Set
    -- The interpretation of ONNX tensors
    ⟦_⟧tensor  : ∀ {sig} → ONNXTensor sig → TensorSemantics ⟦_⟧type sig
    -- The interpretation of ONNX networks
    ⟦_⟧network : ∀ {sig} → ONNXNetwork sig → NetworkSemantics ⟦_⟧type sig
    
    -- The interpretation of the basic ONNX tensor operations at each type
    ⟦_⟧≤   : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type Bool
    ⟦_⟧<   : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type Bool
    ⟦_⟧≥   : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type Bool
    ⟦_⟧>   : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type Bool
    ⟦_⟧=   : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type Bool
    ⟦_⟧≠   : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type Bool
    ⟦_⟧neg : ∀ (τ : ONNXType) → TensorOp1 ⟦ τ ⟧type ⟦ τ ⟧type
    ⟦_⟧add : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type ⟦ τ ⟧type
    ⟦_⟧mul : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type ⟦ τ ⟧type
