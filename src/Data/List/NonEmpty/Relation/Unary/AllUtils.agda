module Data.List.NonEmpty.Relation.Unary.AllUtils where

open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.All
 
import Data.List.Relation.Unary.Any as ListAny
import Data.List.Relation.Unary.All as ListAll
open import Data.List.Relation.Unary.Any as List using (here; there)
open import Data.List.Base using ([]; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Level using (Level; _⊔_)
open import Relation.Unary using (Pred; _⊆_)

private
  variable
    a p : Level
    A : Set a
    P Q : Pred A p
    xs : List⁺ A

map : P ⊆ Q → All P xs → All Q xs
map P⊆Q (px ∷ pxs) = P⊆Q px ∷ ListAll.map P⊆Q pxs
