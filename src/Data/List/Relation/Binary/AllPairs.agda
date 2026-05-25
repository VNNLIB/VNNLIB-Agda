module Data.List.Relation.Binary.AllPairs where

open import Level
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary

private
  variable
    a b ℓ : Level
    A B : Set a
    R : REL A B ℓ
    x : A
    xs ys : List A

data AllPairs {A : Set a} {B : Set b} (R : REL A B ℓ) : List A → List B → Set (a ⊔ b ⊔ ℓ) where
  [] : AllPairs R [] ys
  _∷_ : All (R x) ys → AllPairs R xs ys → AllPairs R (x ∷ xs) ys
