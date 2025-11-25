module VNNLIB.Parser.Monad where

open import Level
open import Data.Bool.Base using (if_then_else_)
open import Data.Maybe.Base using ()
open import Data.String.Base using (String)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.Product.Base as Product using (Σ; _,_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Effect.Monad
open import Function.Base

open import Data.Sum.Effectful.Left String 0ℓ using (monad)

private
  variable
    a b : Level
    A B : Set a
    P Q R : A → Set b

-------------------------
-- Type-checking monad --
-------------------------
-- TODO work out how to get Agda instance arguments working with
-- monad and applicative functions
    
-- The type-checking monad
TCM : ∀ {a} → Set a → Set a
TCM A = String ⊎ A

open RawMonad monad public

open Sum public renaming
  (inj₁ to throw)

traverseTCMList : {A B : Set} → (A → TCM B) → List A → TCM (List B)
traverseTCMList f [] = return []
traverseTCMList f (x ∷ xs) = do
  x' ← f x
  xs' ← traverseTCMList f xs
  return (x' ∷ xs')

---------------
-- Inference --
---------------
-- At certain points in type-checking we need to infer the type of arithmetic
-- expressions. This is a little bit of helper code in continuation-passing
-- code to allow us to express this nicely.


-- A result where the type can be inferred
TypedInference : {A : Set} → (A → Set) → Set
TypedInference {A = A} P = TCM (Σ A P)

mapTypedInference : (∀ {τ : A} → P τ → Q τ) → TypedInference P → TypedInference Q
mapTypedInference f action = do
  result ← action
  return (Product.map₂ f result)

-- A result where the type cannot be inferred
UntypedInference : {A : Set} → (A → Set) → Set
UntypedInference P = ∀ τ → TCM (P τ)

mapUntypedInference : (∀ {τ : A} → P τ → Q τ) → UntypedInference P → UntypedInference Q
mapUntypedInference f infer τ = do
  result ← infer τ
  return (f result)

zipUntypedInference :
  (∀ {τ : A} → P τ → Q τ → R τ) →
  UntypedInference P →
  UntypedInference Q →
  UntypedInference R
zipUntypedInference f x y τ = do
  v1 ← x τ
  v2 ← y τ
  return $ f v1 v2

-- A result where the type may either be inferrable or uninferrable
Inference : {A : Set} → (A → Set) → Set
Inference P = UntypedInference P ⊎ TypedInference P

open Sum public renaming
  ( inj₁ to unknownType
  ; inj₂ to knownType
  )

mapInference : (∀ {τ : A} → P τ → Q τ) → Inference P → Inference Q
mapInference f = Sum.map (mapUntypedInference f) (mapTypedInference f)

resolveInference :
  DecidableEquality A →
  (∀ {τ : A} → P τ → Q τ → R τ) →
  TypedInference P →
  Inference Q →
  TypedInference R
resolveInference {Q = Q} _≟_ f typed x = do
  (τ , e1) ← typed
  e2 ← case x of λ where
    (knownType v) → do
      (τ' , e2) ← v
      case τ' ≟ τ of λ where
        (yes τ'≡τ) → return (subst Q τ'≡τ e2)
        (no  _) → throw "Type mismatch"
    (unknownType v) → v τ
  return (τ , f e1 e2)

zipInference :
  DecidableEquality A →
  (∀ {τ : A} → P τ → Q τ → R τ) →
  Inference P →
  Inference Q →
  Inference R
zipInference ≟ f (unknownType x) (unknownType y) = unknownType $ zipUntypedInference f x y
zipInference ≟ f x               (knownType y)   = knownType $ resolveInference ≟ (flip f) y x
zipInference ≟ f (knownType x)   y               = knownType $ resolveInference ≟ f x y

