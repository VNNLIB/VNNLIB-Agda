
module Data.List.NonEmpty.Relation.Binary.Pointwise where

open import Data.List.Base using ([]; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_)
import Data.List.Relation.Binary.Pointwise as List
open import Level
open import Relation.Binary.Core using (REL)

private
  variable
    a b ℓ : Level
    A B : Set
    
infixr 5 _∷_

data Pointwise {A : Set a} {B : Set b} (R : REL A B ℓ)
               : List⁺ A → List⁺ B → Set (a ⊔ b ⊔ ℓ) where
  _∷_ : ∀ {x y xs ys} (x∼y : R x y) (xs∼ys : List.Pointwise R xs ys) →
        Pointwise R (x ∷ xs) (y ∷ ys)
