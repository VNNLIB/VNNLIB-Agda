
module Data.List.NonEmpty.Relation.Binary.Pointwise where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.List.NonEmpty.Base using (List⁺; _∷_)
open import Data.List.NonEmpty.Properties using ()
import Data.List.Relation.Binary.Pointwise as List
open import Level
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable as Dec
open import Data.Product using (uncurry; _×_; _,_)

private
  variable
    a b ℓ : Level
    A B : Set
    x : A
    xs : List A
    xs⁺ : List⁺ A
    y : B
    ys : List B
    ys⁺ : List⁺ B
    zs⁺ : List⁺ B
    R S T : REL A B ℓ
    
infixr 5 _∷_

data Pointwise {A : Set a} {B : Set b} (R : REL A B ℓ) : List⁺ A → List⁺ B → Set (a ⊔ b ⊔ ℓ) where
  _∷_ : ∀ {x y xs ys} (x∼y : R x y) (xs∼ys : List.Pointwise R xs ys) → Pointwise R (x ∷ xs) (y ∷ ys)

symmetric : Sym R S → Sym (Pointwise R) (Pointwise S)
symmetric sym (x∼y ∷ xs∼ys) = sym x∼y ∷ List.symmetric sym xs∼ys

transitive : Trans R S T → Trans (Pointwise R) (Pointwise S) (Pointwise T)
transitive trans (x∼y ∷ xs∼ys) (y∼z ∷ ys∼zs) = trans x∼y y∼z ∷ List.transitive trans xs∼ys ys∼zs

uncons : Pointwise R (x ∷ xs) (y ∷ ys) → R x y × List.Pointwise R xs ys
uncons (Rxy ∷ Rxsys) = Rxy , Rxsys

∷-injective : ∀ {x y : A} {xs ys : List A} → _≡_ {A = List⁺ A} (x ∷ xs) (y ∷ ys) → x ≡ y × xs ≡ ys
∷-injective refl = refl , refl

decidableEq : DecidableEquality A → DecidableEquality (List⁺ A)
decidableEq _≟_ (x ∷ xs) (y ∷ ys) = Dec.map′
  (uncurry (cong₂ _∷_))
  ∷-injective
  (x ≟ y ×-dec ≡-dec _≟_ xs ys)

decidable : (R? : Decidable R) → Decidable (Pointwise R)
decidable R? (x ∷ xs) (y ∷ ys) = Dec.map′
  (uncurry _∷_)
  uncons
  (R? x y ×-dec List.decidable R? xs ys)
