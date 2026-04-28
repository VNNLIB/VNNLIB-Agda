module Data.RationalUtils where

open import Data.Bool using (Bool; not; _∧_;_∨_)
open import Data.Bool.Properties using (∧-comm)
open import Data.Rational using (ℚ;_≤ᵇ_)
open import Relation.Binary.PropositionalEquality

infix 4 _≥ᵇ_ _>ᵇ_ _<ᵇ_ _=ᵇ_ _≠ᵇ_

_≥ᵇ_ : ℚ → ℚ → Bool
p ≥ᵇ q = q ≤ᵇ p

_>ᵇ_ : ℚ → ℚ → Bool
p >ᵇ q = not (p ≤ᵇ q)

_<ᵇ_ : ℚ → ℚ → Bool
p <ᵇ q = not (q ≤ᵇ p)

_=ᵇ_ : ℚ → ℚ → Bool
p =ᵇ q = (q ≤ᵇ p) ∧ (p ≤ᵇ q)

_≠ᵇ_ : ℚ → ℚ → Bool
p ≠ᵇ q = not ((q ≤ᵇ p) ∧ (p ≤ᵇ q))

=ᵇ-sym : ∀ x y → (x =ᵇ y) ≡ (y =ᵇ x)
=ᵇ-sym x y = ∧-comm (y ≤ᵇ x) (x ≤ᵇ y)

≠ᵇ-sym : ∀ x y → (x ≠ᵇ y) ≡ (y ≠ᵇ x)
≠ᵇ-sym x y = cong not (=ᵇ-sym x y)

