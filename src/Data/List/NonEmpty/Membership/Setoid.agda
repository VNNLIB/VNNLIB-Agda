open import Relation.Binary.Bundles using (Setoid)

module Data.List.NonEmpty.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.List.NonEmpty.Base using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.Any as Any
  using (Any; map; here; there)
open import Data.Product.Base as Product using (∃; _×_; _,_)
open import Function.Base using (_∘_; flip; const)
open import Relation.Binary.Definitions using (_Respects_)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Unary using (Pred)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _∈_ _∉_

_∈_ : A → List⁺ A → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : A → List⁺ A → Set _
x ∉ xs = ¬ x ∈ xs
