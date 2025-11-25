open import ONNX.Syntax
open import ONNX.Semantics

module VNNLIB.Semantics
  {onnxSyntax : NetworkTheorySyntax}
  (onnxSemantics : NetworkTheorySemantics onnxSyntax)
  where

open import Algebra.Core using (Op₂)
open import Data.Bool.ListAction as ListAction using (and)
open import Data.List.Base as List hiding (and)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as All using ()
open import Data.List.Membership.Propositional as ∈
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Data.String.Base hiding (map)
open import Data.Bool.Base renaming (T to True)
open import Data.Fin.Base as Fin using ()
open import Data.Product.Base as Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Function.Base
open import Relation.Nullary.Decidable using (Dec)

open import Relation.Unary using ()
open import Data.Real as ℝ
open import Data.RationalUtils as Real
open import VNNLIB.Syntax onnxSyntax
open import Data.Tensor
open import Data.List.NonEmpty.Relation.Unary.Any as Any⁺ using () renaming (Any to Any⁺)
import Data.List.NonEmpty.Relation.Unary.AllUtils as All⁺
open import Data.List.NonEmpty.Membership.Propositional as ∈⁺

open NetworkTheorySyntax onnxSyntax
open NetworkTheorySemantics onnxSemantics

private
  variable
    Γ : NetworkContext
    τ : ElementType
    d : NetworkDeclaration Γ
    shape : TensorShape

-----------------
-- Environment --
-----------------

InputsValues : NetworkDeclaration Γ → Set
InputsValues d = All⁺ (TensorSemantics ⟦elementType⟧) (typeOfInputs d)

HiddenValues : NetworkDeclaration Γ → Set
HiddenValues d = All (TensorSemantics ⟦elementType⟧) (typeOfHiddenNodes d)

OutputsValues : NetworkDeclaration Γ → Set
OutputsValues d = All⁺ (TensorSemantics ⟦elementType⟧) (typeOfOutputs d)

record NetworkVariableValues (d : NetworkDeclaration Γ) : Set where
  constructor variableValues
  field
    ⟦inputs⟧  : InputsValues d
    ⟦hidden⟧  : HiddenValues d
    ⟦outputs⟧ : OutputsValues d

createNetworkVariableValues :
  NetworkImplementation d →
  InputAssignment d →
  NetworkVariableValues d 
createNetworkVariableValues (networkImplementation network hiddenNodeMapping) inputs = do
  let ⟦inputs⟧ = All⁺.map ⟦theoryTensor⟧ inputs
  let ⟦hidden⟧ = All.map⁺ (All.map (⟦model⟧ network ⟦inputs⟧ ∘ hiddenNode) hiddenNodeMapping)
  let ⟦outputs⟧ = All⁺.map (⟦model⟧ network ⟦inputs⟧) (outputNodes network)
  variableValues ⟦inputs⟧ ⟦hidden⟧ ⟦outputs⟧

Environment : NetworkContext → Set
Environment = AllNetworks NetworkVariableValues

createEnvironment : NetworkImplementations Γ → InputAssignments Γ → Environment Γ
createEnvironment = zipAllNetworks createNetworkVariableValues

--------------------------
-- Assertion components --
--------------------------

module _ (Δ : Environment Γ) where

  ---------------
  -- Variables --
  ---------------

  ⟦constant⟧ : ElementType → Set
  ⟦constant⟧ τ = TensorSemantics ⟦elementType⟧ (tensorType τ [])
  
  ⟦inputVar⟧ : InputElementVariable Γ τ → ⟦constant⟧ τ
  ⟦inputVar⟧ (elementVar _ inputNode indices) = do
    let (_ , _ , variableValues ⟦inputs⟧ _ _ , inputRef) = lookupNetwork Δ inputNode
    let ⟦input⟧ = ∈⁺.lookup ⟦inputs⟧ inputRef
    tensorLookup ⟦input⟧ indices

  ⟦hiddenVar⟧ : HiddenElementVariable Γ τ → ⟦constant⟧ τ
  ⟦hiddenVar⟧ (elementVar _ hiddenNode indices) = do
    let (_ , _ , variableValues _ ⟦hidden⟧ _ , hiddenRef) = lookupNetwork Δ hiddenNode
    let hiddenTensor = All.lookup ⟦hidden⟧ hiddenRef
    tensorLookup hiddenTensor indices
    
  ⟦outputVar⟧ : OutputElementVariable Γ τ → ⟦constant⟧ τ
  ⟦outputVar⟧ (elementVar _ outputNode indices) = do
    let (_ , _ , variableValues _ _ ⟦outputs⟧ , outputRef) = lookupNetwork Δ outputNode
    let outputTensor = ∈⁺.lookup ⟦outputs⟧ outputRef
    tensorLookup outputTensor indices

  -----------------------------
  -- Arithemetic expressions --
  -----------------------------
  
  mutual
    ⟦arithExpr⟧ : ArithExpr Γ τ → ⟦constant⟧ τ
    ⟦arithExpr⟧ (constant  a)  = ⟦theoryTensor⟧ a
    ⟦arithExpr⟧ (inputVar  v)  = ⟦inputVar⟧ v
    ⟦arithExpr⟧ (hiddenVar v)  = ⟦hiddenVar⟧ v
    ⟦arithExpr⟧ (outputVar v)  = ⟦outputVar⟧ v
    ⟦arithExpr⟧ (negate    e)  = ⟦neg⟧ (⟦arithExpr⟧ e)
    ⟦arithExpr⟧ (add (e ∷ es)) = ⟦arithExprList⟧ ⟦add⟧ (⟦arithExpr⟧ e) es
    ⟦arithExpr⟧ (mul (e ∷ es)) = ⟦arithExprList⟧ ⟦mul⟧ (⟦arithExpr⟧ e) es
    ⟦arithExpr⟧ (sub (e ∷ es)) = ⟦neg⟧ (⟦arithExprList⟧ ⟦add⟧ (⟦neg⟧ (⟦arithExpr⟧ e)) es)

    ⟦arithExprList⟧ : ∀ {τ} → Op₂ (⟦constant⟧ τ) → ⟦constant⟧ τ → List (ArithExpr Γ τ) → ⟦constant⟧ τ
    ⟦arithExprList⟧ op e []       = e
    ⟦arithExprList⟧ op e (x ∷ xs) = op (⟦arithExpr⟧ x) (⟦arithExprList⟧ op e xs)

  ⟦compExpr⟧ : CompExpr Γ τ → Bool
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
    ⟦boolExpr⟧ (and (b ∷ bs))  = ⟦boolExprList⟧ _∧_ (⟦boolExpr⟧ b) bs
    ⟦boolExpr⟧ (or  (b ∷ bs))  = ⟦boolExprList⟧ _∨_ (⟦boolExpr⟧ b) bs
    ⟦boolExpr⟧ (comparison (τ , e))  = ⟦compExpr⟧ e

    ⟦boolExprList⟧ : Op₂ Bool → Bool → List (BoolExpr Γ) → Bool
    ⟦boolExprList⟧ op e []       = e
    ⟦boolExprList⟧ op e (x ∷ xs) = op (⟦boolExpr⟧ x) (⟦boolExprList⟧ op e xs)

  ----------------
  -- Assertions --
  ----------------
  
  ⟦assertion⟧ : Assertion Γ → Bool
  ⟦assertion⟧ (assert p) = ⟦boolExpr⟧ p

  ⟦assertionList⟧ : List (Assertion Γ) → Bool
  ⟦assertionList⟧ ps = ListAction.and (List.map ⟦assertion⟧ ps)

-------------
-- Queries --
-------------

QuerySemantics : Set₁
QuerySemantics = (q : Query) → NetworkImplementations (context q) → Set

⟦query⟧ : QuerySemantics
⟦query⟧ (query Γ assertions) networks =
  ∃ λ (assignment : InputAssignments Γ) →
    let Δ = createEnvironment networks assignment in
    True (⟦assertionList⟧ Δ assertions)
