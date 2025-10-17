
module Data.DependentList where

open import Data.List.Base
open import Level

data DepList {a b} {A : Set a} (B : A → Set b) : List A → Set (a ⊔ b) where
  [] : DepList B []
  _∷_ : ∀ {x xs} → B x → DepList B xs → DepList B (x ∷ xs)
