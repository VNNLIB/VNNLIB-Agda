open import ONNX.Syntax

module VNNLIB.Theories.ArithmeticComplexity
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.List using (List; length; []; _∷_ )
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _∷⁺_)  
open import Data.Sum using (_⊎_)
open import Data.Product.Base using (_×_)
open import Relation.Unary using (U)
open import Relation.Binary.PropositionalEquality using (_≡_)


open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax


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
ConstantArithExpr (constant x) = ⊤
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


----------
-- LIN --
----------

-- Determine if an Arithmetic expression has an embedded variable
mutual
  EmbeddedVarArithExpr : ∀ {Γ} → ArithExprPredicate Γ
  EmbeddedVarArithExpr (constant x) = ⊥
  EmbeddedVarArithExpr (negate a)   = EmbeddedVarArithExpr a
  EmbeddedVarArithExpr (add x) = List⁺EmbeddedVarArithExpr x
  EmbeddedVarArithExpr (sub x) = List⁺EmbeddedVarArithExpr x
  EmbeddedVarArithExpr (mul x) = List⁺EmbeddedVarArithExpr x
  EmbeddedVarArithExpr var     = VarArithExpr var

  List⁺EmbeddedVarArithExpr : ∀ {Γ i} → List⁺ (ArithExpr Γ i) → Set
  List⁺EmbeddedVarArithExpr (head ∷⁺ tail) = EmbeddedVarArithExpr head ⊎ ListEmbeddedVarArithExpr tail

  ListEmbeddedVarArithExpr : ∀ {Γ i} → List (ArithExpr Γ i) → Set
  ListEmbeddedVarArithExpr [] = ⊥
  ListEmbeddedVarArithExpr (x ∷ xs) = EmbeddedVarArithExpr x ⊎ ListEmbeddedVarArithExpr xs 

--- Determine if an Arithmetic expression is linear
mutual
  LinearExpression : ∀ {Γ} → ArithExprPredicate Γ
  LinearExpression {Γ} (constant x)  = ConstantArithExpr {Γ} (constant x)
  LinearExpression (negate a)    = LinearExpression a
  LinearExpression (inputVar x)  = VarArithExpr (inputVar x)
  LinearExpression (hiddenVar x) = VarArithExpr (hiddenVar x)
  LinearExpression (outputVar x) = VarArithExpr (outputVar x)
  LinearExpression (add x) = LinearList⁺ArithExpr x
  LinearExpression (sub x) = LinearList⁺ArithExpr x
  LinearExpression (mul x) = LinearList⁺ArithExpr-mult x

  -- Multiplication must have at most 1 embedded variable for linearity
  LinearList⁺ArithExpr-mult : ∀ {Γ i} → List⁺ (ArithExpr Γ i) → Set
  LinearList⁺ArithExpr-mult (head ∷⁺ tail) = LinearListArithExpr-mult (head ∷ tail)
    where
      LinearListArithExpr-mult : ∀ {Γ i} → List (ArithExpr Γ i) → Set
      LinearListArithExpr-mult [] = ⊤
      LinearListArithExpr-mult (x ∷ xs) =
        (EmbeddedVarArithExpr x × (ListEmbeddedVarArithExpr xs → ⊥)) ⊎ ((EmbeddedVarArithExpr x → ⊥) × LinearListArithExpr-mult xs)

  -- Addition and subtraction are linear operations
  LinearList⁺ArithExpr : ∀ {Γ i} → List⁺ (ArithExpr Γ i) → Set
  LinearList⁺ArithExpr (head ∷⁺ tail) = LinearExpression head × LinearListArithExpr tail
    where
      LinearListArithExpr : ∀ {Γ i} → List (ArithExpr Γ i) → Set
      LinearListArithExpr [] = ⊤
      LinearListArithExpr (x ∷ xs) = LinearExpression x × LinearListArithExpr xs
  
-- Assertion comparisons are betweeen linear expressions
LinearArithmetic : AssertionPredicate
LinearArithmetic {Γ} (assert x) = checkBoolExpr Γ LinearExpression LinearExpression x

-- A query that lives in the LIN theory
LinearArithmeticTheory : Theory
LinearArithmeticTheory = AllAssertions LinearArithmetic

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

