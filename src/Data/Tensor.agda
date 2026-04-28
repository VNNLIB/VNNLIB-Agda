module Data.Tensor where

open import Data.Bool.Base
open import Data.Nat as ℕ
open import Data.Fin as Fin
open import Data.List as List
open import Data.List.Properties using (≡-dec)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Rational as ℚ
open import Data.List.Relation.Unary.All
open import Level
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; cong)

private
  variable
    a : Level
    A B C : Set a
    
-- Tensor

TensorShape : Set
TensorShape = List ℕ

_shape-≟_ : DecidableEquality TensorShape
_shape-≟_ = ≡-dec ℕ._≟_

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

mapTensor : ∀ {shape} → (A → B) → Tensor A shape → Tensor B shape
mapTensor f (scalar x) = scalar (f x)
mapTensor f (vector x) = vector (Vec.map (mapTensor f) x)

zipTensor : ∀ {shape} → (A → B → C) → Tensor A shape → Tensor B shape → Tensor C shape
zipTensor f (scalar x) (scalar y) = scalar (f x y)
zipTensor f (vector x) (vector y) = vector (Vec.zipWith (zipTensor f) x y)

comparePointwise : (A → A → Bool) → ∀ {shape} → Tensor A shape → Tensor A shape → Bool
comparePointwise f (scalar x) (scalar y) = f x y
comparePointwise f (vector x) (vector y) = Vec.foldr′ _∧_ true (Vec.zipWith (comparePointwise f) x y)

comparePointwise-sym : ∀ {f g} → (∀ x y → f x y ≡ g y x) → ∀ {shape} (xs ys : Tensor A shape) → comparePointwise f xs ys ≡ comparePointwise g ys xs 
comparePointwise-sym sym (scalar x) (scalar y) = sym x y
comparePointwise-sym sym (vector x) (vector y) = cong (Vec.foldr′ _∧_ true) (zipWith-sym (comparePointwise-sym sym) x y)
  where
  zipWith-sym : ∀ {A B : Set a} {f g : A → A → B} → (∀ x y → f x y ≡ g y x) → ∀ {n} (xs ys : Vec A n) → Vec.zipWith f xs ys ≡ Vec.zipWith g ys xs
  zipWith-sym sym [] [] = _≡_.refl
  zipWith-sym sym (x ∷ xs) (y ∷ ys) = Eq.cong₂ _∷_ (sym x y) (zipWith-sym sym xs ys)

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
