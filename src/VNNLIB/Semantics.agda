open import ONNX.Syntax
open import ONNX.Semantics

module VNNLIB.Semantics
  {onnxSyntax : NetworkTheorySyntax}
  (onnxSemantics : NetworkTheorySemantics onnxSyntax)
  where

open import Algebra.Core using (Op₂)
open import Data.Bool.ListAction using (and)
open import Data.List.Base as List hiding (and)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Data.String.Base hiding (map)
open import Data.Bool.Base renaming (T to True)
open import Data.Fin.Base as Fin using ()
open import Data.Product.Base as Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Function.Base
open import Relation.Nullary.Decidable using (Dec)

open import Relation.Unary using ()
open import Data.Real as ℝ
open import Data.RationalUtils as Real
open import VNNLIB.Syntax onnxSyntax
open import Data.Tensor
open import Data.List.NonEmpty.Relation.Unary.Any as Any⁺ using () renaming (Any to Any⁺)
import Data.List.NonEmpty.Relation.Unary.AllUtils as All⁺
open import Data.List.NonEmpty.Membership.Propositional as ∈ using (_∈_)

open NetworkTheorySyntax onnxSyntax
open NetworkTheorySemantics onnxSemantics

private
  variable
    Γ : NetworkContext
    τ : TheoryType
    shape : TensorShape

---------------------------
-- Abstract environments --
---------------------------

mapEnvironment : {P Q : NetworkPredicate} → (∀ {Γ} {d : NetworkDeclaration Γ} → P d → Q d) → AllNetworks P Γ → AllNetworks Q Γ
mapEnvironment f []       = []
mapEnvironment f (Δ ∷ Δₙ) = mapEnvironment f Δ ∷ f Δₙ

zipEnvironment : {P Q R : NetworkPredicate} → (∀ {Γ} {d : NetworkDeclaration Γ} → P d → Q d → R d) → AllNetworks P Γ → AllNetworks Q Γ → AllNetworks R Γ
zipEnvironment f [] []       = []
zipEnvironment f (Δ₁ ∷ Δ₁ₙ) (Δ₂ ∷ Δ₂ₙ) = zipEnvironment f Δ₁ Δ₂ ∷ f Δ₁ₙ Δ₂ₙ

lookupInEnvironment : {P Q : NetworkPredicate} → AllNetworks P Γ → AnyNetwork Q Γ → Σ NetworkContext (λ Γ' → Σ (NetworkDeclaration Γ') (λ n → P n × Q n))
lookupInEnvironment (Δ ∷ Δₙ) (here Px)    = _ , _ , Δₙ , Px
lookupInEnvironment (Δ ∷ Δₙ) (there Pxs) = lookupInEnvironment Δ Pxs

----------------------
-- Runtime networks --
----------------------

NetworkImplementation : NetworkPredicate
NetworkImplementation d = TheoryNetwork (typeOfNetwork d)

NetworkImplementations : NetworkContext → Set
NetworkImplementations = AllNetworks NetworkImplementation

-----------------------
-- Input assignments --
-----------------------

NetworkInputAssignment : NetworkPredicate
NetworkInputAssignment d = All⁺ TheoryTensor (typeOfInputs d)

NetworkInputAssignments : NetworkContext → Set
NetworkInputAssignments = AllNetworks NetworkInputAssignment

-----------------
-- Environment --
-----------------

record NetworkVariableValues (d : NetworkDeclaration Γ) : Set where
  constructor variableValues
  field
    ⟦inputs⟧  : InputsSemantics ⟦theoryType⟧ (typeOfInputs d)
    ⟦outputs⟧ : OutputsSemantics ⟦theoryType⟧ (typeOfOutputs d)

createNetworkVariableValues : ∀ {d : NetworkDeclaration Γ} → NetworkImplementation d → NetworkInputAssignment d → NetworkVariableValues d 
createNetworkVariableValues network inputs = do
  let ⟦inputs⟧ = All⁺.map ⟦theoryTensor⟧ inputs
  let ⟦network⟧ = ⟦theoryNetwork⟧ network
  let ⟦outputs⟧ = ⟦network⟧ ⟦inputs⟧
  variableValues ⟦inputs⟧ ⟦outputs⟧

Environment : NetworkContext → Set
Environment = AllNetworks NetworkVariableValues

createEnvironment : NetworkImplementations Γ → NetworkInputAssignments Γ → Environment Γ
createEnvironment = zipEnvironment createNetworkVariableValues

--------------------------
-- Assertion components --
--------------------------

module _ {Γ : NetworkContext} (Δ : Environment Γ) where

  ---------------
  -- Variables --
  ---------------

  ⟦constant⟧ : TheoryType → Set
  ⟦constant⟧ τ = TensorSemantics ⟦theoryType⟧ (tensorType τ [])
  
  ⟦inputVar⟧ : ∀ {τ} → InputElementVariable Γ τ → ⟦constant⟧ τ
  ⟦inputVar⟧ (elementVar _ inputNode indices) = do
    let (_ , _ , variableValues ⟦inputs⟧ _ , inputRef) = lookupInEnvironment Δ inputNode
    let ⟦input⟧ = ∈.lookup ⟦inputs⟧ inputRef
    tensorLookup ⟦input⟧ indices

  ⟦outputVar⟧ : ∀ {τ} → OutputElementVariable Γ τ → ⟦constant⟧ τ
  ⟦outputVar⟧ (elementVar _ outputNode indices) = do
    let (_ , _ , variableValues _ ⟦outputs⟧ , outputRef) = lookupInEnvironment Δ outputNode
    let outputTensor = ∈.lookup ⟦outputs⟧ outputRef
    tensorLookup outputTensor indices

  -----------------------------
  -- Arithemetic expressions --
  -----------------------------
  
  mutual
    ⟦arithExpr⟧ : ArithExpr Γ τ → ⟦constant⟧ τ
    ⟦arithExpr⟧ (constant  a)  = ⟦theoryTensor⟧ a
    ⟦arithExpr⟧ (inputVar  v)  = ⟦inputVar⟧ v
    ⟦arithExpr⟧ (outputVar v)  = ⟦outputVar⟧ v
    ⟦arithExpr⟧ (negate    e)  = ⟦neg⟧ (⟦arithExpr⟧ e)
    ⟦arithExpr⟧ (add (e ∷ es)) = ⟦arithExprList⟧ ⟦add⟧ (⟦arithExpr⟧ e) es
    ⟦arithExpr⟧ (mul (e ∷ es)) = ⟦arithExprList⟧ ⟦mul⟧ (⟦arithExpr⟧ e) es
    ⟦arithExpr⟧ (sub (e ∷ es)) = ⟦neg⟧ (⟦arithExprList⟧ ⟦add⟧ (⟦neg⟧ (⟦arithExpr⟧ e)) es)

    ⟦arithExprList⟧ : ∀ {τ} → Op₂ (⟦constant⟧ τ) → ⟦constant⟧ τ → List (ArithExpr Γ τ) → ⟦constant⟧ τ
    ⟦arithExprList⟧ op e []       = e
    ⟦arithExprList⟧ op e (x ∷ xs) = op (⟦arithExpr⟧ x) (⟦arithExprList⟧ op e xs)

  ⟦compExpr⟧ : ∀ {τ} → CompExpr Γ τ → Bool
  ⟦compExpr⟧ (greaterThan  e₁ e₂) = ⟦>⟧ (⟦arithExpr⟧ e₁) (⟦arithExpr⟧ e₂)
  ⟦compExpr⟧ (lessThan     e₁ e₂) = ⟦<⟧ (⟦arithExpr⟧ e₁) (⟦arithExpr⟧ e₂)
  ⟦compExpr⟧ (greaterEqual e₁ e₂) = ⟦≥⟧ (⟦arithExpr⟧ e₁) (⟦arithExpr⟧ e₂)
  ⟦compExpr⟧ (lessEqual    e₁ e₂) = ⟦<⟧ (⟦arithExpr⟧ e₁) (⟦arithExpr⟧ e₂)
  ⟦compExpr⟧ (notEqual     e₁ e₂) = ⟦≠⟧ (⟦arithExpr⟧ e₁) (⟦arithExpr⟧ e₂)
  ⟦compExpr⟧ (equal        e₁ e₂) = ⟦=⟧ (⟦arithExpr⟧ e₁) (⟦arithExpr⟧ e₂)

  -------------------------
  -- Boolean expressions --
  -------------------------

  mutual  
    ⟦boolExpr⟧ : BoolExpr Γ → Bool
    ⟦boolExpr⟧ (literal  b)        = b
    ⟦boolExpr⟧ (andExpr (b ∷ bs))  = ⟦boolExprList⟧ _∧_ (⟦boolExpr⟧ b) bs
    ⟦boolExpr⟧ (orExpr  (b ∷ bs))  = ⟦boolExprList⟧ _∨_ (⟦boolExpr⟧ b) bs
    ⟦boolExpr⟧ (compExpr (τ , e))  = ⟦compExpr⟧ e

    ⟦boolExprList⟧ : Op₂ Bool → Bool → List (BoolExpr Γ) → Bool
    ⟦boolExprList⟧ op e []       = e
    ⟦boolExprList⟧ op e (x ∷ xs) = op (⟦boolExpr⟧ x) (⟦boolExprList⟧ op e xs)

  ----------------
  -- Assertions --
  ----------------
  
  ⟦assertion⟧ : Assertion Γ → Bool
  ⟦assertion⟧ (assert p) = ⟦boolExpr⟧ p

  ⟦assertionList⟧ : List (Assertion Γ) → Bool
  ⟦assertionList⟧ ps = and (List.map ⟦assertion⟧ ps)

-------------
-- Queries --
-------------

QuerySemantics : Set₁
QuerySemantics = (q : Query) → NetworkImplementations (context q) → Set

⟦query⟧ : QuerySemantics
⟦query⟧ (query Γ assertions) networks =
  ∃ λ (assignment : NetworkInputAssignments Γ) →
    let Δ = createEnvironment networks assignment in
    True (⟦assertionList⟧ Δ assertions)
