module utils where

open import Data.Bool using (Bool; not; _∧_;_∨_)

module Real where
  open import Data.Rational using (ℚ;_≤ᵇ_)
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

module Float64 where
  open import Agda.Builtin.Float
  infix 4 _≥ᵇ_ _>ᵇ_ _<ᵇ_ _=ᵇ_ _≠ᵇ_ _≤ᵇ_

  _=ᵇ_ : Float → Float → Bool
  p =ᵇ q = primFloatEquality p q
  
  _≠ᵇ_ : Float → Float → Bool
  p ≠ᵇ q = primFloatInequality p q

  _<ᵇ_ : Float → Float → Bool
  p <ᵇ q = primFloatLess p q

  _≤ᵇ_ : Float → Float → Bool
  p ≤ᵇ q = (p <ᵇ q) ∨ (p =ᵇ q) 
  
  _≥ᵇ_ : Float → Float → Bool
  p ≥ᵇ q = not (p <ᵇ q)
  
  _>ᵇ_ : Float → Float → Bool
  p >ᵇ q = q <ᵇ p
 


open import Data.Maybe using (Maybe; just; nothing)
open import Data.List
open import Data.List.NonEmpty using (List⁺; fromList)
open import Data.String using (String)
open import Level using (0ℓ)
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error)
open import Effect.Monad
open RawMonad monad

-- Utils for the Error Monad --
convertMaybeToResult : {A : Set} → Maybe A → Result A
convertMaybeToResult (just x) = return x
convertMaybeToResult nothing = error "Empty List"

convertListToList⁺ : {A : Set} → List A → Result (List⁺ A)
convertListToList⁺ lst = do
  let convertedList = fromList lst
  res ← convertMaybeToResult (convertedList)
  return res

open import Data.Nat using (ℕ;_<?_)
open import Data.Fin using (Fin; fromℕ<; zero; suc)
open import Relation.Nullary using (yes;no)

-- Util for converting a natural number to a fin --
toFin : (n m : ℕ) → Maybe (Fin n)
toFin n m with m <? n
... | yes p = just (fromℕ< p)
... | no _  = nothing

-- Convert a lookup into a list with a predicate into Any
open import Relation.Unary using (Pred)
open import Data.List.Relation.Unary.Any using (Any;here;there)
indexToAny : ∀ {a p} {A : Set a} {P : Pred A p} {xs : List A} → (i : Fin (length xs)) → P (lookup xs i) → Any P xs
indexToAny  {xs = x ∷ xs} zero    px = here px
indexToAny  {xs = x ∷ xs} (suc i) px = there (indexToAny i px)
