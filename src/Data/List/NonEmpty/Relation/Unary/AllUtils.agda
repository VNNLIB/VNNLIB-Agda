module Data.List.NonEmpty.Relation.Unary.AllUtils where

open import Data.List.NonEmpty as NonEmpty using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.All
open import Data.List.NonEmpty.Relation.Unary.Any as Any using (Any; here; there)

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.Any as ListAny
open import Data.List.Relation.Unary.All as ListAll using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.List.Relation.Binary.Pointwise as ListPointwise using ([]; _∷_)
open import Data.List.NonEmpty.Relation.Binary.Pointwise
open import Data.List.Relation.Unary.Any as List using (here; there)
open import Data.List.Base using ([]; _∷_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
open import Data.Product.Base using (_×_; _,_; ∃; uncurry)
open import Level using (Level; _⊔_)
open import Relation.Unary
open import Function.Base

private
  variable
    a p : Level
    A B : Set a
    P Q R : Pred A p
    xs ys : List⁺ A

map : P ⊆ Q → All P xs → All Q xs
map P⊆Q (px ∷ pxs) = P⊆Q px ∷ ListAll.map P⊆Q pxs

map⁺ : ∀ {f : A → B} → All (P ∘ f) xs → All P (NonEmpty.map f xs)
map⁺ (p ∷ ps) = p ∷ ListAll.map⁺ ps

map⁻ : ∀ {f : A → B} → All P (NonEmpty.map f xs) → All (P ∘ f) xs
map⁻ (p ∷ ps) = p ∷ ListAll.map⁻ ps

lookupAny : All P xs → (i : Any Q xs) → (P ∩ Q) (Any.lookup i)
lookupAny (px ∷ pxs) (here qx) = px , qx
lookupAny (px ∷ pxs) (there i) = ListAll.lookupAny pxs i

lookupWith : ∀[ P ⇒ Q ⇒ R ] → All P xs → (i : Any Q xs) → R (Any.lookup i)
lookupWith f pxs i = uncurry f (lookupAny pxs i)

lzipWith : ∀ {R : A → B → Set} → (∀ {x y} → P x → R x y → Q y) → ∀ {xs : List A} {ys : List B} → ListAll.All P xs → ListPointwise.Pointwise R xs ys → ListAll.All Q ys
lzipWith f [] [] = []
lzipWith f (Px ∷ Pxs) (Rxy ∷ Rxsys) = f Px Rxy ∷ lzipWith f Pxs Rxsys

zipWith : {R : A → B → Set} → (∀ {x y} → P x → R x y → Q y) → All P xs → Pointwise R xs ys → All Q ys
zipWith f (Pfxy ∷ Pfxsys) (Rxy ∷ Rxsys) = f Pfxy Rxy ∷ lzipWith f Pfxsys Rxsys

