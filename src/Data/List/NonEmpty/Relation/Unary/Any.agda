module Data.List.NonEmpty.Relation.Unary.Any where

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
    
------------------------------------------------------------------------
-- Definition

-- Given a predicate P, then Any P xs means that every element in xs
-- satisfies P. See `Relation.Unary` for an explanation of predicates.

data Any {A : Set a} (P : Pred A p) : Pred (List⁺ A) (a ⊔ p) where
  here : ∀ {x xs} (px : P x) → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : List.Any P xs) → Any P (x ∷ xs)

map : P ⊆ Q → Any P ⊆ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (List.map g pxs)

satisfied : Any P xs → ∃ λ x → P x
satisfied (here px)  = _ , px
satisfied (there pxs) = List.satisfied pxs

satisfied-all-list : ∀ {xs} → ListAny.Any P xs → ListAll.All Q xs → ∃ λ x → P x × Q x
satisfied-all-list (here  px)  (qx ListAll.∷ qxs) = _ , px , qx
satisfied-all-list (there pxs) (qx ListAll.∷ qxs) = satisfied-all-list pxs qxs

satisfied-all : Any P xs → All Q xs → ∃ λ x → P x × Q x
satisfied-all (here  px)  (qx ∷ qxs) = _ , px , qx
satisfied-all (there pxs) (qx ∷ qxs) = satisfied-all-list pxs qxs

lookup : {P : Pred A p} → Any P xs → A
lookup {xs = x ∷ _} (here px) = x
lookup (there pxs) = ListAny.lookup pxs
