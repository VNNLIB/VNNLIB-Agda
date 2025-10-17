module Data.Tensor where

open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.List as List
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Rational as ℚ


-- Tensor

TensorShape : Set
TensorShape = List ℕ

data TensorIndices : TensorShape → Set where
 empty : TensorIndices []
 non-empty : {head : ℕ} → {tail : List ℕ} → Fin head →  TensorIndices tail → TensorIndices (head ∷ tail) 

-- This representation of a tensor is taken from the `Mat` data structure by
-- Alexis King in https://gist.github.com/lexi-lambda/5bec3f33b1db4269fc129242b53b5f43#file-matrix-agda
data Tensor (Σ : Set) : TensorShape → Set where
  scalar : Σ → Tensor Σ []
  vector : {head : ℕ} → {tail : List ℕ} → Vec (Tensor Σ tail) head → Tensor Σ (head ∷ tail)


tensorLookup : ∀ {shape} {A : Set} → TensorIndices shape → Tensor A shape → A
tensorLookup {[]} empty (scalar x) = x
tensorLookup {dim ∷ shape} (non-empty idx idxs) (vector x) = tensorLookup idxs (Vec.lookup x idx)



-- Example usage
private
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
