module Data.Tensor where

open import Data.Bool.Base
open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.List as List
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Rational as ℚ
open import Data.List.Relation.Unary.All
open import Level

private
  variable
    a : Level
    A B C : Set a
    
-- Tensor

TensorShape : Set
TensorShape = List ℕ

TensorIndices : TensorShape → Set
TensorIndices shape = All Fin shape

open All public
  using ([]; _∷_)

-- This representation of a tensor is taken from the `Mat` data structure by
-- Alexis King in https://gist.github.com/lexi-lambda/5bec3f33b1db4269fc129242b53b5f43#file-matrix-agda
data Tensor (A : Set) : TensorShape → Set where
  scalar : A → Tensor A []
  vector : {head : ℕ} {tail : List ℕ} → Vec (Tensor A tail) head → Tensor A (head ∷ tail)

tensorLookup : ∀ {shape} {A : Set} → Tensor A shape → TensorIndices shape → Tensor A []
tensorLookup x          []            = x
tensorLookup (vector x) (idx ∷ idxs) = tensorLookup (Vec.lookup x idx) idxs

postulate mapTensor : ∀ {shape} → (A → B) → Tensor A shape → Tensor B shape

postulate zipTensor : ∀ {shape} → (A → B → C) → Tensor A shape → Tensor B shape → Tensor C shape

postulate comparePointwise : (A → A → Bool) → ∀ {shape} → Tensor A shape → Tensor A shape → Bool

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
  testIndex = (# 1) ∷ ((# 1) ∷ ((# 1) ∷ []))

  testElement : Tensor ℚ []
  testElement = tensorLookup testTensor testIndex

  -- Scalar

  testTensorₛ : Tensor ℚ []
  testTensorₛ = scalar 1ℚ

  testIndex₁ : TensorIndices []
  testIndex₁ = []
