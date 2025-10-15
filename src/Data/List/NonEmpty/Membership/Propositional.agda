module Data.List.NonEmpty.Membership.Propositional {a} {A : Set a} where

open import Relation.Binary.PropositionalEquality using (setoid; refl)
import Data.List.Relation.Unary.All as ListAll
open import Data.List.NonEmpty.Relation.Unary.All
open import Data.List.NonEmpty.Relation.Unary.Any using (here; there)
open import Data.List.NonEmpty
open import Level
open import Relation.Unary using (Pred)

import Data.List.NonEmpty.Membership.Setoid as SetoidMembership

------------------------------------------------------------------------
-- Re-export contents of setoid membership

open SetoidMembership (setoid A) public

-- TOGO in All when move to stdlib

private
  variable
    p : Level
    P : Pred A p
    xs : List⁺ A
    
lookup : All P xs → ∀ {x} → x ∈ xs → P x
lookup (px ∷ pxs) (here refl)   = px
lookup (px ∷ pxs) (there x∈xs) = ListAll.lookup pxs x∈xs
