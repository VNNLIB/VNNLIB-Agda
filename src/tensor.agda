module tensor where

open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.List as List
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Rational as ℚ
open import vnnlib-types


-- Tensor

TensorShape : Set
TensorShape = List ℕ

data TensorIndices : TensorShape → Set where
 empty : TensorIndices []
 non-empty : {head : ℕ} → {tail : List ℕ} → Fin head →  TensorIndices tail → TensorIndices (head ∷ tail) 

data Tensor (Σ : Set) : TensorShape → Set where
  scalar : Σ → Tensor Σ []
  vector : {head : ℕ} → {tail : List ℕ} → Vec (Tensor Σ tail) head → Tensor Σ (head ∷ tail)


tensorLookup : ∀ {shape} {A : Set} → TensorIndices shape → Tensor A shape → A
tensorLookup {[]} empty (scalar x) = x
tensorLookup {dim ∷ shape} (non-empty idx idxs) (vector x) = tensorLookup idxs (Vec.lookup x idx)

tensorLookupET : ∀ {shape} {elementType : ElementType} → TensorIndices shape → Tensor (ElementTypeToSet elementType) shape → ElementTypeToSet elementType
tensorLookupET {[]} empty (scalar x) = x
tensorLookupET {dim ∷ shape} (non-empty idx idxs) (vector x) = tensorLookup idxs (Vec.lookup x idx)


-- Example usage
testSide₁ : Tensor ℚ (2 ∷ 2 ∷ [])
testSide₁ = vector (vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷
                 vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷ [])

testSide₂ : Tensor ℚ (2 ∷ 2 ∷ [])
testSide₂ = vector (vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷
                 vector (scalar 1ℚ ∷ scalar 1ℚ ∷ []) ∷ [])

testTensor : Tensor ℚ (2 ∷ 2 ∷ 2 ∷ [])
testTensor = vector (testSide₁ ∷ testSide₂ ∷ [])

testIndex : TensorIndices (2 ∷ 2 ∷ 2 ∷ [])
testIndex = non-empty (# 1) (non-empty (# 1) (non-empty ((# 1)) empty))

testElement : ℚ
testElement = tensorLookup testIndex testTensor

-- Scalar

testTensorₛ : Tensor ℚ []
testTensorₛ = scalar 1ℚ

testIndex₁ : TensorIndices []
testIndex₁ = empty
