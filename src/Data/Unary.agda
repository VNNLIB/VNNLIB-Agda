module Data.Unary {i} {I : Set i} where

open import Relation.Unary.Indexed using (IPred)
open import Relation.Unary using (_∈_; _⊆_)
open import Level
open import Data.Sum.Base

private
  variable
    a p q ℓ ℓ₁ ℓ₂ : Level
    Aᵢ : I → Set a
    
infixr 6 _∪_
_∪_ : IPred Aᵢ ℓ₁ → IPred Aᵢ ℓ₂ → IPred Aᵢ _
(P ∪ Q) = λ xᵢ → xᵢ ∈ P ⊎ xᵢ ∈ Q
