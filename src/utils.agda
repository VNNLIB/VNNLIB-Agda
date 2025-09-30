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


open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺; fromList)
open import Data.String using (String)
open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error)
open import Effect.Monad

open RawMonad monad

convertMaybeToResult : {A : Set} → Maybe A → Result A
convertMaybeToResult (just x) = return x
convertMaybeToResult nothing = error "Empty List"

convertListToList⁺ : {A : Set} → List A → Result (List⁺ A)
convertListToList⁺ lst = do
  let convertedList = fromList lst
  res ← convertMaybeToResult (convertedList)
  return res

open import Data.Nat using (ℕ; _<_; _≤_; _<?_)
open import Data.Fin using (Fin; fromℕ<)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary

toFin : (n m : ℕ) → Maybe (Fin n)
toFin n m with m <? n
... | yes p = just (fromℕ< p)
... | no _  = nothing
