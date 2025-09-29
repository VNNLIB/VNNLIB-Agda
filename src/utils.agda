module utils where

open import Data.Rational using (ℚ; _≤ᵇ_)
open import Data.Bool using (Bool; not; _∧_)

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

lookup-map : {A B : Set} → (f : A → B) → (xs : List A) → (i : Fin (length xs)) → lookup (map f xs) (cast (sym (length-map f xs)) i) ≡ f (lookup xs i)
lookup-map f (x ∷ a) zero = refl
lookup-map f (x ∷ a) (suc b) = lookup-map f a b