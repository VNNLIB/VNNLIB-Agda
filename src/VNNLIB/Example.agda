open import ONNX.Syntax
open import ONNX.Semantics
open import ONNX.Parser
import ONNX.Real

module VNNLIB.Example
  {onnxSyntax : NetworkTheorySyntax}
  (onnxSemantics : NetworkTheorySemantics onnxSyntax)
  (open ONNX.Real onnxSyntax onnxSemantics)
  (realNetworkSemantics : RealNetworkSemantics)
  where

open import Data.String.Base using (String; fromList)
open import Data.Nat.Base
open import Data.Bool.Base using (T)
open import Data.Product as Prod using (∃; _,_)
open import Data.Rational
open import Data.Fin
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.Any using (Any; here)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
import Data.List.Properties as List
import Data.Bool.ListAction as ListAction
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)
open import Agda.Builtin.Int
open import Data.Integer.Base
open import Data.Sign.Base
open import Level using (0ℓ)
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Data.Empty using (⊥)
open import Function
open import Data.Tensor
open import Data.RationalUtils

open import VNNLIB.Syntax realSyntax
open import VNNLIB.Semantics (realSemantics realNetworkSemantics)

---------------------------------------------
-- Example 1 : Representing a simple query --
---------------------------------------------

-- Suppose we have the following VNNLIB query:
{-
  "
  (vnnlib-version <2.0>)
  
  (declare-network N
	(declare-input X Real [3])
	(declare-output Y Real [1])
  )
  
  (assert (and (<= 0 X[0]) (>= 1 X[0])))
  (assert (<= 0 Y[0]))
  "
-}

-- Below is the native Agda VNNLIB representation of this query.
-- It is is intrinsically well-typed so that if you e.g. change the
-- size of the dimension in the declare-output from `1` to `0` then
-- you will get an error.

query1 : Query
query1 = query
  ((declareNetwork
    "N"
    (declareInput "X" (tensorType real (3 ∷ [])) ∷ [])
    []
    (declareOutput "Y" (tensorType real (1 ∷ [])) ∷ [])
    none) ∷ [])  
  (assert (comparison (lessEqual (constant (scalar 0ℚ)) Y[0])) ∷ [])
  (none ∷ [])
  where
  -- Variables are represented as pointers first into the list of the
  -- network declarations, and then into the relevant input/output/hidden list.
  -- In this way it is impossible to write ill-scoped queries.
  Y[0] = outputVar (elementVar (here (here refl)) (zero ∷ []))

-----------------------------------------------------
-- Example 2: Proving soundness of an optimisation --
-----------------------------------------------------

-- We now demonstrate how we can prove the soundness of a simple optimisation.
-- The optimisation in question is that we take every assertion
-- and reverse the direction of every inequality in it:
-- 
--  e.g. (<= X[0] Y[0]) becomes (>= Y[0] X[0])

----------------------------------------
-- Step 1: Defining the transformation

-- First we define the transformation, working our way up
-- from flipping a single comparison expression to flipping
-- every comparison expression in an entire query.

private
  variable
    Γ : NetworkDeclarations
    
flipComparison : ∀ {Γ τ} → CompExpr Γ τ → CompExpr Γ τ
flipComparison (greaterThan x y)  = lessThan y x
flipComparison (lessThan x y)     = greaterThan y x
flipComparison (greaterEqual x y) = lessEqual y x
flipComparison (lessEqual x y)    = greaterEqual y x
flipComparison (notEqual x y)     = notEqual y x
flipComparison (equal x y)        = equal y x

mutual
  flipBoolExpr : BoolExpr Γ → BoolExpr Γ
  flipBoolExpr (literal x)    = literal x
  flipBoolExpr (comparison x) = comparison (flipComparison x)
  flipBoolExpr (and xs) = and (flipBoolExprList⁺ xs)
  flipBoolExpr (or xs) = or (flipBoolExprList⁺ xs)

  flipBoolExprList : List (BoolExpr Γ) → List (BoolExpr Γ)
  flipBoolExprList [] = []
  flipBoolExprList (x ∷ xs) = flipBoolExpr x ∷ flipBoolExprList xs

  flipBoolExprList⁺ : List⁺ (BoolExpr Γ) → List⁺ (BoolExpr Γ)
  flipBoolExprList⁺ (x ∷ xs) = flipBoolExpr x ∷ flipBoolExprList xs

flipAssertion : Assertion Γ → Assertion Γ
flipAssertion (assert b) = assert (flipBoolExpr b)

flipAssertions : List (Assertion Γ) → List (Assertion Γ)
flipAssertions = List.map flipAssertion

flipComparisons : Query → Query
flipComparisons (query networks assertions validEq) = query networks (flipAssertions assertions) validEq
    
-- Flipping the model is a no-op but we still have to reconstruct
-- the record manually otherwise the type-checker doesn't see it.
flipModels : ∀ q → QueryModels q → QueryModels (flipComparisons q)
flipModels q (queryModels networkImplementations implementationsRespectEquivalences) =
              queryModels networkImplementations implementationsRespectEquivalences

----------------------------------------------------
-- Step 2: Proving soundness of the transformation

-- Again we just work our way through proving that each transformation
-- of the syntax preserves the computed semantics.

-- Helper lemma
Σ-⇔ : {A : Set} {P Q : A → Set} → (∀ {x} → P x ≡ Q x) → ∃ P ⇔ ∃ Q
Σ-⇔ P≡Q = mk⇔ (Prod.map₂ (castEq P≡Q)) (Prod.map₂ (castEq (Eq.sym P≡Q)))
  where
  castEq : {A B : Set} → A ≡ B → A → B
  castEq refl x = x

module _ (Γ : NetworkDeclarations) (Δ : Environment Γ) where

  flipComparison-sound : ∀ c → ⟦compExpr⟧ Δ c ≡ ⟦compExpr⟧ Δ (flipComparison c)
  flipComparison-sound (greaterThan  e₁ e₂) = comparePointwise-sym (λ x y → refl) (⟦arithExpr⟧ Δ e₁) (⟦arithExpr⟧ Δ e₂)
  flipComparison-sound (lessThan     e₁ e₂) = comparePointwise-sym (λ x y → refl) (⟦arithExpr⟧ Δ e₁) (⟦arithExpr⟧ Δ e₂)
  flipComparison-sound (greaterEqual e₁ e₂) = comparePointwise-sym (λ x y → refl) (⟦arithExpr⟧ Δ e₁) (⟦arithExpr⟧ Δ e₂)
  flipComparison-sound (lessEqual    e₁ e₂) = comparePointwise-sym (λ x y → refl) (⟦arithExpr⟧ Δ e₁) (⟦arithExpr⟧ Δ e₂)
  flipComparison-sound (notEqual     e₁ e₂) = comparePointwise-sym ≠ᵇ-sym          (⟦arithExpr⟧ Δ e₁) (⟦arithExpr⟧ Δ e₂)
  flipComparison-sound (equal        e₁ e₂) = comparePointwise-sym =ᵇ-sym          (⟦arithExpr⟧ Δ e₁) (⟦arithExpr⟧ Δ e₂)

  mutual
    flipBoolExpr-sound : ∀ e → ⟦boolExpr⟧ Δ e ≡ ⟦boolExpr⟧ Δ (flipBoolExpr e)
    flipBoolExpr-sound (literal x)     = refl
    flipBoolExpr-sound (comparison x)  = flipComparison-sound x
    flipBoolExpr-sound (and (x ∷ xs)) = flipBoolExprList-sound xs (flipBoolExpr-sound x)
    flipBoolExpr-sound (or (x ∷ xs))  = flipBoolExprList-sound xs (flipBoolExpr-sound x)

    flipBoolExprList-sound : ∀ {e f op} es → e ≡ f →
                             ⟦boolExprList⟧ Δ op e es ≡ ⟦boolExprList⟧ Δ op f (flipBoolExprList es)
    flipBoolExprList-sound [] eq = eq
    flipBoolExprList-sound {op = op} (x ∷ es) eq = Eq.cong₂ op (flipBoolExpr-sound x) (flipBoolExprList-sound es eq)

  flipAssertion-sound : ∀ assertion → ⟦assertion⟧ Δ assertion ≡ ⟦assertion⟧ Δ (flipAssertion assertion)
  flipAssertion-sound (assert x) = flipBoolExpr-sound x

  flipAssertions-sound : ∀ assertions → ⟦assertionList⟧ Δ assertions ≡ ⟦assertionList⟧ Δ (flipAssertions assertions)
  flipAssertions-sound assertions =
    Eq.cong ListAction.and
      (Eq.trans
        (List.map-cong flipAssertion-sound assertions)
        (List.map-∘ assertions)
      )

-- The final result says that for any query `q` and set of models `models` then
-- flipping all the comparisons in the query doesn't change the meaning of the query.
flipComparisons-sound : ∀ q models → ⟦query⟧ q models ⇔ ⟦query⟧ (flipComparisons q) (flipModels q models)
flipComparisons-sound (query networks assertions validEq) models =
  Σ-⇔ (λ {is} → Eq.cong T (flipAssertions-sound networks (createEnvironment _ _) assertions ))
