open import ONNX.Syntax

module VNNLIB.Syntax
  (theorySyntax : NetworkTheorySyntax)
  where

open import Data.List.Base as List using (List; []; map)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺)
open import Data.String.Base using (String)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Unit.Base using (⊤)
open import Level
open import Relation.Unary.Indexed using (IPred)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (const)

open import Data.List.NonEmpty.Membership.Propositional using (_∈_)
open import Data.Real
open import Data.Tensor using (TensorShape; TensorIndices)

open NetworkTheorySyntax theorySyntax

------------------
-- Declarations --
------------------

Name : Set
Name = String

------------------------
-- Input declarations --
------------------------

record InputDeclaration : Set where
  constructor declareInput
  field
    inputName : Name
    inputType : TensorType TheoryType

open InputDeclaration public

-------------------------
-- Output declarations --
-------------------------

record OutputDeclaration : Set where
  constructor declareOutput
  field
    outputName : Name
    outputType : TensorType TheoryType

open OutputDeclaration public

--------------
-- Networks --
--------------
--
-- Network declarations may contain back-references to earlier
-- network declarations via `equal-to` and `isomorphic-to` statements.
-- Therefore it is necessary to define these concepts mutually.

mutual

  ----------------------
  -- Network contexts --
  ----------------------

  data NetworkContext : Set where
    [] : NetworkContext
    _∷_ : (Γ : NetworkContext) → NetworkDeclaration Γ → NetworkContext

  ------------------------
  -- Network definition --
  ------------------------
  
  record NetworkDeclaration (Γ : NetworkContext) : Set where
    constructor declareNetwork
    field
      networkName    : Name
      networkInputs  : List⁺ InputDeclaration
      networkOutputs : List⁺ OutputDeclaration

  typeOfInputs : ∀ {Γ} → NetworkDeclaration Γ → InputTypes TheoryType
  typeOfInputs n = List⁺.map inputType (NetworkDeclaration.networkInputs n)

  typeOfOutputs : ∀ {Γ} → NetworkDeclaration Γ → OutputTypes TheoryType
  typeOfOutputs n = List⁺.map outputType (NetworkDeclaration.networkOutputs n)

  typeOfNetwork : ∀ {Γ} → NetworkDeclaration Γ → NetworkType TheoryType
  typeOfNetwork n = networkType (typeOfInputs n) (typeOfOutputs n)

  ---------------------------------------
  -- Restrictions on network variables --
  ---------------------------------------
 
  NetworkPredicate : Set₁
  NetworkPredicate = IPred NetworkDeclaration 0ℓ

  postulate ValidEqualToTarget : NetworkPredicate

  postulate ValidIsomorphicToTarget : NetworkPredicate

  HasInputMatching : TensorType TheoryType → NetworkPredicate
  HasInputMatching type network = type ∈ typeOfInputs network

  HasOutputMatching : TensorType TheoryType → NetworkPredicate
  HasOutputMatching type network = type ∈ typeOfOutputs network

  -----------------------
  -- Network variables --
  -----------------------

  -- A reference to a network in the context that satisfies some property P
  data AnyNetwork (P : NetworkPredicate) : NetworkContext → Set where
    here : ∀ {ns n} → P n → AnyNetwork P (ns ∷ n)
    there : ∀ {ns n} → AnyNetwork P ns → AnyNetwork P (ns ∷ n)

  -- Associates every declared network `d` in the context with some dependent value of type `P d`
  data AllNetworks (P : NetworkPredicate) : NetworkContext → Set where
    [] : AllNetworks P []
    _∷_ : ∀ {Γ d} (Δ : AllNetworks P Γ) (Δₙ : P d) → AllNetworks P (Γ ∷ d)

  -- A reference to a network that is equal to the current network
  EqualNetworkVariable : NetworkContext → Set
  EqualNetworkVariable = AnyNetwork ValidEqualToTarget

  -- A reference to a network that is isomorphic to the current network
  IsomorphicNetworkVariable : NetworkContext → Set
  IsomorphicNetworkVariable = AnyNetwork ValidIsomorphicToTarget

open NetworkDeclaration public

-------------
-- Numbers --
-------------

Number : TheoryType → Set
Number τ = TheoryTensor (tensorType τ [])

--------------------
-- Node variables --
--------------------  

NodeVariableSort : Set₁
NodeVariableSort = NetworkContext → TensorType TheoryType → Set

InputVariable : NodeVariableSort
InputVariable Γ sig = AnyNetwork (HasInputMatching sig) Γ

OutputVariable : NodeVariableSort
OutputVariable Γ sig = AnyNetwork (HasOutputMatching sig) Γ

-----------------------
-- Element variables --
-----------------------

record ElementVariable (NodeVariable : NodeVariableSort) (Γ : NetworkContext) (τ : TheoryType) : Set where
  constructor elementVar
  field
    shape   : TensorShape
    node    : NodeVariable Γ (tensorType τ shape)
    indices : TensorIndices shape

InputElementVariable : NetworkContext → TheoryType → Set
InputElementVariable = ElementVariable InputVariable

OutputElementVariable : NetworkContext → TheoryType  → Set
OutputElementVariable = ElementVariable OutputVariable

--------------------------
-- Assertion components --
--------------------------

module _ (Γ : NetworkContext) where

  ----------------------------
  -- Arithmetic expressions --
  ----------------------------
  
  data ArithExpr (τ : TheoryType) : Set where
    constant  : Number τ → ArithExpr τ
    negate    : ArithExpr τ → ArithExpr τ 
    inputVar  : InputElementVariable Γ τ → ArithExpr τ
    outputVar : OutputElementVariable Γ τ → ArithExpr τ
    add       : List⁺ (ArithExpr τ) → ArithExpr τ
    sub       : List⁺ (ArithExpr τ) → ArithExpr τ
    mul       : List⁺ (ArithExpr τ) → ArithExpr τ

  ----------------------------
  -- Comparison expressions --
  ----------------------------

  data CompExpr (τ : TheoryType) : Set where
    greaterThan  : ArithExpr τ → ArithExpr τ → CompExpr τ
    lessThan     : ArithExpr τ → ArithExpr τ → CompExpr τ
    greaterEqual : ArithExpr τ → ArithExpr τ → CompExpr τ
    lessEqual    : ArithExpr τ → ArithExpr τ → CompExpr τ
    notEqual     : ArithExpr τ → ArithExpr τ → CompExpr τ
    equal        : ArithExpr τ → ArithExpr τ → CompExpr τ

  -------------------------
  -- Boolean expressions --
  -------------------------

  data BoolExpr : Set where
    literal    : Bool → BoolExpr
    comparison : Σ TheoryType CompExpr → BoolExpr
    and        : List⁺ BoolExpr → BoolExpr
    or         : List⁺ BoolExpr → BoolExpr

  ----------------
  -- Assertions --
  ----------------

  data Assertion : Set where
    assert : BoolExpr → Assertion

-------------
-- Queries --
-------------

record Query : Set where
  constructor query
  field
    context : NetworkContext
    assertions : List (Assertion context)

open Query public
