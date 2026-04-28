open import ONNX.Syntax

module VNNLIB.Syntax
  (theorySyntax : NetworkTheorySyntax)
  where

open import Data.List.Base as List using (List; []; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Data.String.Base using (String)
open import Data.Maybe using (Maybe; just; nothing; Is-nothing)
import Data.Maybe.Relation.Unary.All as Maybe
open import Data.Fin.Base as Fin using (Fin)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₂)
open import Data.Unit.Base using (⊤)
open import Level
open import Relation.Unary.Indexed using (IPred)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (const)

open import Data.List.NonEmpty.Relation.Unary.Any using () renaming (Any to Any⁺)
open import Data.List.NonEmpty.Membership.Propositional using () renaming (_∈_ to _∈⁺_)
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
    inputType : TensorType ElementType

open InputDeclaration public

-------------------------
-- Hidden declarations --
-------------------------

record HiddenDeclaration : Set where
  constructor declareHidden
  field
    hiddenName : Name
    hiddenType : TensorType ElementType
    nodeOutputName : NodeOutputName
    
open HiddenDeclaration public

-------------------------
-- Output declarations --
-------------------------

record OutputDeclaration : Set where
  constructor declareOutput
  field
    outputName : Name
    outputType : TensorType ElementType

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
    inductive
    constructor declareNetwork
    field
      networkName        : Name
      inputDeclarations  : List⁺ InputDeclaration
      hiddenDeclarations : List HiddenDeclaration
      outputDeclarations : List⁺ OutputDeclaration
      equivalence        : Maybe (NetworkEquivalence Γ (typeOfNetworkRecord inputDeclarations outputDeclarations))

  typeOfInputs : ∀ {Γ} → NetworkDeclaration Γ → InputTypes ElementType
  typeOfInputs d = List⁺.map inputType (NetworkDeclaration.inputDeclarations d)

  typeOfHiddenNodes : ∀ {Γ} → NetworkDeclaration Γ → HiddenNodeTypes ElementType
  typeOfHiddenNodes d = List.map hiddenType (NetworkDeclaration.hiddenDeclarations d)

  typeOfOutputs : ∀ {Γ} → NetworkDeclaration Γ → OutputTypes ElementType
  typeOfOutputs d = List⁺.map outputType (NetworkDeclaration.outputDeclarations d)

  typeOfNetwork : ∀ {Γ} → NetworkDeclaration Γ → NetworkType ElementType
  typeOfNetwork d = networkType (typeOfInputs d) (typeOfOutputs d)

  typeOfNetworkRecord : List⁺ InputDeclaration → List⁺ OutputDeclaration → NetworkType ElementType
  typeOfNetworkRecord inputs outputs = networkType (List⁺.map inputType inputs) (List⁺.map outputType outputs)

  ----------------------------------
  -- Network congruence statement --
  ----------------------------------
  
  data NetworkEquivalence (Γ : NetworkContext) (type : NetworkType ElementType) : Set where
    equal-to      : EqualNetworkVariable Γ type → NetworkEquivalence Γ type
    isomorphic-to : IsomorphicNetworkVariable Γ type → NetworkEquivalence Γ type

  ---------------------------------------
  -- Restrictions on network variables --
  ---------------------------------------
 
  NetworkPredicate : Set₁
  NetworkPredicate = IPred NetworkDeclaration 0ℓ

  -- A valid equal network reference has the same network type
  record ValidEqualToTarget {Γ} (δ : NetworkType ElementType) (target : NetworkDeclaration Γ) : Set where
    inductive
    field
      targetIsNotAnEquivalence : Is-nothing (NetworkDeclaration.equivalence target)
      targetTypesMatch : NetworkTypesMatch δ (typeOfNetwork target)

  -- A valid isomorphic network reference has the same network shape
  record ValidIsomorphicToTarget {Γ} (δ : NetworkType ElementType) (target : NetworkDeclaration Γ) : Set where
    inductive
    field
      targetIsNotAnEquivalence : Is-nothing (NetworkDeclaration.equivalence target)
      targetShapesMatch : NetworkShapesMatch δ (typeOfNetwork target) 

  -----------------------
  -- Network variables --
  -----------------------

  -- A reference to a network in the context that satisfies some property P
  data AnyNetwork (P : NetworkPredicate) : NetworkContext → Set where
    here : ∀ {ns n} → P n → AnyNetwork P (ns ∷ n)
    there : ∀ {ns n} → AnyNetwork P ns → AnyNetwork P (ns ∷ n)

  -- A reference to a network that is equal to the current network
  EqualNetworkVariable : NetworkContext → NetworkType ElementType → Set
  EqualNetworkVariable Γ type = AnyNetwork (ValidEqualToTarget type) Γ

  -- A reference to a network that is isomorphic to the current network
  IsomorphicNetworkVariable : NetworkContext → NetworkType ElementType → Set
  IsomorphicNetworkVariable Γ type = AnyNetwork (ValidIsomorphicToTarget type) Γ

open NetworkDeclaration public

------------------------------------
-- Network declaration predicates --
------------------------------------

HasInputDeclarationMatching : TensorType ElementType → NetworkPredicate
HasInputDeclarationMatching type network = type ∈⁺ typeOfInputs network

HasHiddenDeclarationMatching : TensorType ElementType → NetworkPredicate
HasHiddenDeclarationMatching type network = type ∈ typeOfHiddenNodes network

HasOutputDeclarationMatching : TensorType ElementType → NetworkPredicate
HasOutputDeclarationMatching type network = type ∈⁺ typeOfOutputs network

--------------------
-- Node variables --
--------------------  

TensorVariableType : Set₁
TensorVariableType = NetworkContext → TensorType ElementType → Set

InputVariable : TensorVariableType
InputVariable Γ δ = AnyNetwork (HasInputDeclarationMatching δ) Γ

HiddenVariable : TensorVariableType
HiddenVariable Γ δ = AnyNetwork (HasHiddenDeclarationMatching δ) Γ

OutputVariable : TensorVariableType
OutputVariable Γ δ = AnyNetwork (HasOutputDeclarationMatching δ) Γ

-----------------------
-- Element variables --
-----------------------

record ElementVariable (TensorVariable : TensorVariableType) (Γ : NetworkContext) (τ : ElementType) : Set where
  constructor elementVar
  field
    shape   : TensorShape
    node    : TensorVariable Γ (tensorType τ shape)
    indices : TensorIndices shape

InputElementVariable : NetworkContext → ElementType → Set
InputElementVariable = ElementVariable InputVariable

HiddenElementVariable : NetworkContext → ElementType  → Set
HiddenElementVariable = ElementVariable HiddenVariable

OutputElementVariable : NetworkContext → ElementType  → Set
OutputElementVariable = ElementVariable OutputVariable

-------------
-- Numbers --
-------------

Number : ElementType → Set
Number τ = TheoryTensor (tensorType τ [])

--------------------------
-- Assertion components --
--------------------------

module _ (Γ : NetworkContext) where

  ----------------------------
  -- Arithmetic expressions --
  ----------------------------
  
  data ArithExpr (τ : ElementType) : Set where
    constant  : Number τ → ArithExpr τ
    negate    : ArithExpr τ → ArithExpr τ 
    inputVar  : InputElementVariable Γ τ → ArithExpr τ
    hiddenVar : HiddenElementVariable Γ τ → ArithExpr τ
    outputVar : OutputElementVariable Γ τ → ArithExpr τ
    add       : List⁺ (ArithExpr τ) → ArithExpr τ
    sub       : List⁺ (ArithExpr τ) → ArithExpr τ
    mul       : List⁺ (ArithExpr τ) → ArithExpr τ

  ----------------------------
  -- Comparison expressions --
  ----------------------------

  data CompExpr (τ : ElementType) : Set where
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
    comparison : Σ ElementType CompExpr → BoolExpr
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

----------------------
-- Environment --
----------------------

private
  variable
    Γ : NetworkContext
    d : NetworkDeclaration Γ
    γ : NetworkType ElementType
    
-- Associates every declared network `d` in the context with some dependent value of type `P d`
data AllNetworks (P : NetworkPredicate) : NetworkContext → Set where
  [] : AllNetworks P []
  _∷_ : ∀ {Γ d} (Δ : AllNetworks P Γ) (Δₙ : P d) → AllNetworks P (Γ ∷ d)

zipAllNetworks :
  ∀ {Γ} {P Q R : NetworkPredicate} →
  (∀ {Γ} {d : NetworkDeclaration Γ} → P d → Q d → R d) →
  AllNetworks P Γ →
  AllNetworks Q Γ →
  AllNetworks R Γ
zipAllNetworks f [] []       = []
zipAllNetworks f (Δ₁ ∷ Δ₁ₙ) (Δ₂ ∷ Δ₂ₙ) = zipAllNetworks f Δ₁ Δ₂ ∷ f Δ₁ₙ Δ₂ₙ

lookupNetwork :
  ∀ {P Q : NetworkPredicate} →
  AllNetworks P Γ →
  AnyNetwork Q Γ →
  Σ NetworkContext (λ Γ' → Σ (NetworkDeclaration Γ') (λ d → P d × Q d))
lookupNetwork (Δ ∷ Δₙ) (here Px)    = _ , _ , Δₙ , Px
lookupNetwork (Δ ∷ Δₙ) (there Pxs) = lookupNetwork Δ Pxs

----------------------
-- Runtime networks --
----------------------

NetworkImplementations : NetworkContext → Set
NetworkImplementations = AllNetworks (λ d → Model (typeOfNetwork d))


mutual
  CorrespondingHiddenNode : ∀ {γ} → Model γ → HiddenDeclaration → Set
  CorrespondingHiddenNode model h = NodeOutput model (nodeOutputName h) (hiddenType h)

  record NetworkImplementation (d : NetworkDeclaration Γ) : Set where
    constructor networkImplementation
    field
      model             : Model (typeOfNetwork d)
      hiddenNodeMapping : All (CorrespondingHiddenNode model) (hiddenDeclarations d)
      modelEquivalence  : Maybe.All (ModelsEquivalent {!!} model) (equivalence d)

  ModelsEquivalent : NetworkImplementations Γ → Model γ → NetworkEquivalence Γ γ → Set
  ModelsEquivalent models model (equal-to networkVar)      = ModelsEqual model {!!} --(proj₂ (proj₂ (lookupNetwork models networkVar)))
  ModelsEquivalent models model (isomorphic-to networkVar) = ModelsIsomorphic model {!!} --((proj₂ (proj₂ (lookupNetwork models networkVar))))
  
  ModelsEqual : Model γ → (NetworkImplementation d × ValidEqualToTarget γ d) → Set
  ModelsEqual N (target , targetValid) = N ≡[ targetTypesMatch targetValid ] model target
    where open NetworkImplementation; open ValidEqualToTarget
    
  ModelsIsomorphic : Model γ → (NetworkImplementation d × ValidIsomorphicToTarget γ d) → Set
  ModelsIsomorphic N₁ (target , targetValid) = N₁ ↭[ targetShapesMatch targetValid ] model target
    where open NetworkImplementation; open ValidIsomorphicToTarget

-----------------------
-- Input assignments --
-----------------------

InputAssignment : NetworkPredicate
InputAssignment d = All⁺ TheoryTensor (typeOfInputs d)

InputAssignments : NetworkContext → Set
InputAssignments = AllNetworks InputAssignment
