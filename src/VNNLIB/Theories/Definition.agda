open import ONNX.Syntax

module VNNLIB.Theories.Definition
  (networkSyntax : NetworkTheorySyntax)
  where

open import VNNLIB.Syntax networkSyntax

-- A theory is a predicate over a query
Theory : Set₁
Theory = Query → Set

-- An interpretation of a theory set is a mapping of each
-- element in the set to a theory
record Interpretation (TheorySet : Set) : Set₁ where
  field
    interpretation : TheorySet → Theory

-- Use instance arguments to map any theory in a theory set to
-- its interpretation
_∈_ :
  {TheorySet : Set}
  {{_ : Interpretation TheorySet}} →
  Query →
  TheorySet →
  Set
_∈_ {{interp}} q theory = Interpretation.interpretation interp theory q


---------------
-- Utilities --
---------------

open import Relation.Unary.Indexed using (IPred)
open import Relation.Unary using (Pred)
open import Level
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (head; tail)
open import Data.Product.Base using (_×_;_,_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)

AtMostOne : ∀ {A : Set} → Pred A 0ℓ → List A → Set
AtMostOne P [] = ⊤
AtMostOne P (x ∷ xs) = (P x × All (λ y → P y → ⊥) xs) ⊎ ((P x → ⊥) × AtMostOne P xs)

NetworksPredicate : Set₁
NetworksPredicate = Pred NetworkContext⁺ 0ℓ

AssertionPredicate : Set₁
AssertionPredicate = IPred Assertion 0ℓ

AllAssertions : AssertionPredicate → Query → Set
AllAssertions P (query _ assertions) = All P assertions

-------------------------------------
-- Traverse Arithmetic Expressions --
-------------------------------------

ArithExprPredicate : NetworkContext → Set₁
ArithExprPredicate Γ = IPred (ArithExpr Γ) 0ℓ

module _ (Γ : NetworkContext) (P₁ P₂ : ArithExprPredicate Γ) where
  satisfiesBothArithExpr : ∀ {τ} → CompExpr Γ τ → Set
  satisfiesBothArithExpr (greaterThan x x₁)  = P₁ x × P₂ x₁
  satisfiesBothArithExpr (lessThan x x₁)     = P₁ x × P₂ x₁
  satisfiesBothArithExpr (greaterEqual x x₁) = P₁ x × P₂ x₁
  satisfiesBothArithExpr (lessEqual x x₁)    = P₁ x × P₂ x₁
  satisfiesBothArithExpr (notEqual x x₁)     = P₁ x × P₂ x₁
  satisfiesBothArithExpr (equal x x₁)        = P₁ x × P₂ x₁
  
  mutual
    satisfiesArithExpr-list : List (BoolExpr Γ) → Set
    satisfiesArithExpr-list [] = ⊤
    satisfiesArithExpr-list (x ∷ a) = satisfiesArithExpr x × satisfiesArithExpr-list a
  
    satisfiesArithExpr : BoolExpr Γ → Set
    satisfiesArithExpr (literal x) = ⊤
    satisfiesArithExpr (comparison (_ , snd)) = satisfiesBothArithExpr snd
    satisfiesArithExpr (and x) = satisfiesArithExpr (x .head) × satisfiesArithExpr-list (x .tail)
    satisfiesArithExpr (or x)  = satisfiesArithExpr (x .head) × satisfiesArithExpr-list (x .tail)
