open import ONNX.Syntax

module VNNLIB.Theories.ArithmeticComplexity
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.Nat using (ℕ)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.List using (List; length; []; _∷_ )
open import Data.List.NonEmpty
open import Data.Product.Base using (_×_;_,_)
open import Data.Sum using (_⊎_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level
open import Relation.Unary.Indexed using (IPred)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)


open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax


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
  checkCompExpr : ∀ {τ} → CompExpr Γ τ → Set
  checkCompExpr (greaterThan x x₁)  = P₁ x × P₂ x₁
  checkCompExpr (lessThan x x₁)     = P₁ x × P₂ x₁
  checkCompExpr (greaterEqual x x₁) = P₁ x × P₂ x₁
  checkCompExpr (lessEqual x x₁)    = P₁ x × P₂ x₁
  checkCompExpr (notEqual x x₁)     = P₁ x × P₂ x₁
  checkCompExpr (equal x x₁)        = P₁ x × P₂ x₁
  
  mutual
    checkListBoolExpr : List (BoolExpr Γ) → Set
    checkListBoolExpr [] = ⊤
    checkListBoolExpr (x ∷ a) = checkBoolExpr x × checkListBoolExpr a
  
    checkBoolExpr : BoolExpr Γ → Set
    checkBoolExpr (literal x) = ⊤
    checkBoolExpr (comparison (_ , snd)) = checkCompExpr snd
    checkBoolExpr (and x) = checkBoolExpr (x .head) × checkListBoolExpr (x .tail)
    checkBoolExpr (or x)  = checkBoolExpr (x .head) × checkListBoolExpr (x .tail)

----------------
-- Theory set --
----------------

data ArithmeticComplexity : Set where
  BND  : ArithmeticComplexity
  OUTC : ArithmeticComplexity
  LIN  : ArithmeticComplexity
  POLY : ArithmeticComplexity

----------
-- BND --
----------

ConstantArithExpr : ∀ {Γ} → ArithExprPredicate Γ
ConstantArithExpr (constant _) = ⊤
ConstantArithExpr _ = ⊥

VarArithExpr : ∀ {Γ} → ArithExprPredicate Γ
VarArithExpr (inputVar x) = ⊤
VarArithExpr (hiddenVar x) = ⊤
VarArithExpr (outputVar x) = ⊤
VarArithExpr _ = ⊥

ConstantOrVarArithExpr : ∀ {Γ} → ArithExprPredicate Γ
ConstantOrVarArithExpr x = ConstantArithExpr x ⊎ VarArithExpr x

-- Assertion comparisons only include constants and variables, not comparing two variables
BoundedVariables : AssertionPredicate
BoundedVariables {Γ} (assert x) =
  checkBoolExpr Γ ConstantArithExpr ConstantOrVarArithExpr x ⊎ checkBoolExpr Γ ConstantOrVarArithExpr ConstantArithExpr x

-- A query that lives in the BND theory
BoundedVariablesTheory : Theory
BoundedVariablesTheory = AllAssertions BoundedVariables

-----------
-- OUTC --
-----------

-- Assertion comparisons only include constants and variables
OutputComparisons : AssertionPredicate
OutputComparisons {Γ} (assert x) = checkBoolExpr Γ ConstantOrVarArithExpr ConstantOrVarArithExpr x

-- A query that lives in the OUTC theory
OutputComparisonsTheory : Theory
OutputComparisonsTheory = AllAssertions OutputComparisons


-----------
-- LIN --
-----------

LinearExpression : ∀ {Γ} → ArithExprPredicate Γ
LinearExpression a = {!!}

-- Assertion comparisons only include constants and variables
LinearArithmetic : AssertionPredicate
LinearArithmetic {Γ} (assert x) = checkBoolExpr Γ LinearExpression LinearExpression x

-- A query that lives in the LIN theory
LinearArithmeticTheory : Theory
LinearArithmeticTheory = AllAssertions OutputComparisons

----------
-- POLY --
----------

-- Every query lives in the POLY theory
PolynomialArithmeticTheory : Theory
PolynomialArithmeticTheory = U

--------------------
-- Interpretation --
--------------------

instance
   MultipleNetworksInterpretation : Interpretation ArithmeticComplexity
   MultipleNetworksInterpretation = record
     { interpretation = λ
       { BND  → BoundedVariablesTheory
       ; OUTC → OutputComparisonsTheory
       ; LIN  → LinearArithmeticTheory
       ; POLY → PolynomialArithmeticTheory
       }
     }

