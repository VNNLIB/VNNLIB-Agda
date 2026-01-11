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

-------------------------------------
-- Traverse Arithmetic Expressions --
-------------------------------------

ArithExprPredicate : NetworkContext → Set₁
ArithExprPredicate Γ = IPred (ArithExpr Γ) 0ℓ

module _ (Γ : NetworkContext) (P : ArithExprPredicate Γ)  where
  checkCompExpr : ∀ {τ} → CompExpr Γ τ → Set
  checkCompExpr (greaterThan x x₁) = P x × P x₁
  checkCompExpr (lessThan x x₁) = P x × P x₁
  checkCompExpr (greaterEqual x x₁) = P x × P x₁
  checkCompExpr (lessEqual x x₁) = P x × P x₁
  checkCompExpr (notEqual x x₁) = P x × P x₁
  checkCompExpr (equal x x₁) = P x × P x₁
  
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

-- An Arithmetic expression that is either a constant or variable
NoArithOps : ∀ {Γ} → ArithExprPredicate Γ
NoArithOps (constant x) = ⊤
NoArithOps (inputVar x) = ⊤
NoArithOps (hiddenVar x) = ⊤
NoArithOps (outputVar x) = ⊤
NoArithOps _ = ⊥

BoundedVariables : AssertionPredicate
BoundedVariables {Γ} (assert x) = checkBoolExpr Γ NoArithOps x

-- A query that lives in the BND theory
BoundedVariablesTheory : Theory
BoundedVariablesTheory (query _ assertions) = All BoundedVariables assertions

{-
-----------
-- OUTC --
-----------

-- A query where all networks are equal
MultipleEqualNetworks : NetworksPredicate
MultipleEqualNetworks (networks ∷⁺ x) = NonEquivalentNetwork x × AllNetworks EqualNetwork networks

-- A query that lives in the OUTC theory
MultipleEqualNetworksTheory : Theory
MultipleEqualNetworksTheory (query networks _) = MultipleEqualNetworks networks

-----------
-- LIN --
-----------

-- A network that is equal to another network is also in the isomorphic theory
MultipleIsomorphicNetworks : NetworksPredicate
MultipleIsomorphicNetworks (networks ∷⁺ x) = NonEquivalentNetwork x × AllNetworks TheoryIsomorphicNetwork networks
  where
    TheoryIsomorphicNetwork : NetworkPredicate
    TheoryIsomorphicNetwork network = IsomorphicNetwork network ⊎ EqualNetwork network

-- A query that lives in the LIN theory
MultipleIsomorphicNetworksTheory : Theory
MultipleIsomorphicNetworksTheory (query networks _) = MultipleIsomorphicNetworks networks


----------
-- POLY --
----------

-- Every query lives in the POLY theory
MultipleNetworksTheory : Theory
MultipleNetworksTheory = U

--------------------
-- Interpretation --
--------------------

instance
   MultipleNetworksInterpretation : Interpretation ArithmeticComplexity
   MultipleNetworksInterpretation = record
     { interpretation = λ
       { BND  → SingleNetworkTheory
       ; OUTC → MultipleEqualNetworksTheory
       ; LIN → MultipleIsomorphicNetworksTheory
       ; POLY  → MultipleNetworksTheory
       }
     }
-}
