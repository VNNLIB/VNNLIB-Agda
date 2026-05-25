open import ONNX.Syntax

module VNNLIB.Syntax
  (theorySyntax : NetworkTheorySyntax)
  where

open import Data.List.Base as List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookupAny)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)
open import Data.String.Base using (String)
open import Data.Maybe using (Maybe; just; nothing; Is-nothing)
import Data.Maybe.Relation.Unary.All as Maybe
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₂)
open import Data.Unit.Base using (⊤)
open import Data.Sum using (_⊎_)
open import Level
open import Relation.Unary.Indexed using (IPred)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Function.Base using (const)

open import Data.List.NonEmpty.Relation.Unary.Any using () renaming (Any to Any⁺)
open import Data.List.NonEmpty.Membership.Propositional using () renaming (_∈_ to _∈⁺_)
open import Data.Real
open import Data.List.Relation.Binary.AllPairs using (AllPairs)
open import Data.Tensor using (TensorShape; TensorIndices)

open NetworkTheorySyntax theorySyntax

--------------------------
-- Network Declarations --
--------------------------

Name : Set
Name = String

------------------------
-- Input declarations

record InputDeclaration : Set where
  constructor declareInput
  field
    inputName : Name
    inputType : TensorType ElementType

open InputDeclaration public

-------------------------
-- Hidden declarations

record HiddenDeclaration : Set where
  constructor declareHidden
  field
    hiddenName : Name
    hiddenType : TensorType ElementType
    nodeOutputName : NodeOutputName
    
open HiddenDeclaration public

-------------------------
-- Output declarations

record OutputDeclaration : Set where
  constructor declareOutput
  field
    outputName : Name
    outputType : TensorType ElementType

open OutputDeclaration public

----------------------------------
-- Network equivalence statement

-- Note that we don't store network equivalence references as pointers back
-- into the network context, as the resulting mutual inductive definitions
-- where `NetworkDeclaration` depends on `NetworkContext` and thereby itself,
-- becomes a unwieldy to work with.
data NetworkEquivalence : Set where
  none          : NetworkEquivalence
  equal-to      : Name → NetworkEquivalence
  isomorphic-to : Name → NetworkEquivalence

------------------------
-- Network declaration

record NetworkDeclaration : Set where
  inductive
  constructor declareNetwork
  field
    networkName        : Name
    inputDeclarations  : List⁺ InputDeclaration
    hiddenDeclarations : List HiddenDeclaration
    outputDeclarations : List⁺ OutputDeclaration
    equivalence        : NetworkEquivalence

open NetworkDeclaration public

typeOfInputs : NetworkDeclaration → InputTypes ElementType
typeOfInputs d = List⁺.map inputType (inputDeclarations d)

typeOfHiddenNodes : NetworkDeclaration → HiddenNodeTypes ElementType
typeOfHiddenNodes d = List.map hiddenType (hiddenDeclarations d)

typeOfOutputs : NetworkDeclaration → OutputTypes ElementType
typeOfOutputs d = List⁺.map outputType (outputDeclarations d)
 
typeOfNetwork : NetworkDeclaration → NetworkType ElementType
typeOfNetwork d = networkType (typeOfInputs d) (typeOfOutputs d)

----------------------
-- Network contexts

NetworkDeclarations : Set
NetworkDeclarations = List NetworkDeclaration

---------------------------------------
-- Restrictions on network variables --

NetworkPredicate : Set₁
NetworkPredicate = NetworkDeclaration → Set

HasInputDeclarationMatching : TensorType ElementType → NetworkPredicate
HasInputDeclarationMatching type network = type ∈⁺ typeOfInputs network

HasHiddenDeclarationMatching : TensorType ElementType → NetworkPredicate
HasHiddenDeclarationMatching type network = type ∈ typeOfHiddenNodes network

HasOutputDeclarationMatching : TensorType ElementType → NetworkPredicate
HasOutputDeclarationMatching type network = type ∈⁺ typeOfOutputs network

HiddenNodePairCompatible : HiddenDeclaration → HiddenDeclaration → Set
HiddenNodePairCompatible h₁ h₂ = nodeOutputName h₁ ≢ nodeOutputName h₂ ⊎ hiddenType h₁ ≡ hiddenType h₂
  
----------------------------
-- Equivalence statements --
----------------------------
-- Proof terms that indicate that the network equivalence statements point to a
-- compatible network.

-- A valid equal network reference has the same network type
record ValidEqualToTarget (name : Name) (d : NetworkDeclaration) (target : NetworkDeclaration) : Set where
  constructor validEqualTo
  field
    targetIsNotAnEquivalence : NetworkDeclaration.equivalence target ≡ none
    targetTypesMatch : NetworkTypesMatch (typeOfNetwork d) (typeOfNetwork target)
    targetNamesMatch : name ≡ networkName target
    targetHiddenNodesCompatible : AllPairs HiddenNodePairCompatible (hiddenDeclarations d) (hiddenDeclarations target)

-- A valid isomorphic network reference has the same network shape
record ValidIsomorphicToTarget (name : Name) (d : NetworkDeclaration) (target : NetworkDeclaration) : Set where
  constructor validIsomorphicTo
  field
    targetIsNotAnEquivalence : NetworkDeclaration.equivalence target ≡ none
    targetShapesMatch : NetworkShapesMatch (typeOfNetwork d) (typeOfNetwork target)
    targetNamesMatch : name ≡ networkName target

data ValidNetworkEquivalence (Γ : NetworkDeclarations) (d : NetworkDeclaration) : NetworkEquivalence → Set where
  none          : ValidNetworkEquivalence Γ d none
  equal-to      : ∀ {name} → Any (ValidEqualToTarget name d)      Γ → ValidNetworkEquivalence Γ d (equal-to name)
  isomorphic-to : ∀ {name} → Any (ValidIsomorphicToTarget name d) Γ → ValidNetworkEquivalence Γ d (isomorphic-to name)

data ValidNetworkEquivalences : NetworkDeclarations → Set where
  [] : ValidNetworkEquivalences []
  _∷_ : ∀ {d ds} →
        ValidNetworkEquivalence ds d (equivalence d) →
        ValidNetworkEquivalences ds →
        ValidNetworkEquivalences (d ∷ ds)

----------------
-- Assertions --
----------------

----------------------
-- Tensor variables

TensorVariableType : Set₁
TensorVariableType = NetworkDeclarations → TensorType ElementType → Set

InputVariable : TensorVariableType
InputVariable Γ δ = Any (HasInputDeclarationMatching δ) Γ

HiddenVariable : TensorVariableType
HiddenVariable Γ δ = Any (HasHiddenDeclarationMatching δ) Γ

OutputVariable : TensorVariableType
OutputVariable Γ δ = Any (HasOutputDeclarationMatching δ) Γ

-----------------------
-- Element variables

record ElementVariable
  (TensorVariable : TensorVariableType)
  (Γ : NetworkDeclarations)
  (τ : ElementType) : Set where
  
  constructor elementVar
  field
    {shape} : TensorShape
    node    : TensorVariable Γ (tensorType τ shape)
    indices : TensorIndices shape

InputElementVariable : NetworkDeclarations → ElementType → Set
InputElementVariable = ElementVariable InputVariable

HiddenElementVariable : NetworkDeclarations → ElementType  → Set
HiddenElementVariable = ElementVariable HiddenVariable

OutputElementVariable : NetworkDeclarations → ElementType  → Set
OutputElementVariable = ElementVariable OutputVariable

----------------------
-- Numeric literals

NumericLiteral : ElementType → Set
NumericLiteral τ = TheoryTensor (tensorType τ [])

----------------------------
-- Arithmetic expressions

data ArithExpr (Γ : NetworkDeclarations) (τ : ElementType) : Set where
  constant  : NumericLiteral τ → ArithExpr Γ τ
  negate    : ArithExpr Γ τ → ArithExpr Γ τ 
  inputVar  : InputElementVariable Γ τ → ArithExpr Γ τ
  hiddenVar : HiddenElementVariable Γ τ → ArithExpr Γ τ
  outputVar : OutputElementVariable Γ τ → ArithExpr Γ τ
  add       : List⁺ (ArithExpr Γ τ) → ArithExpr Γ τ
  sub       : List⁺ (ArithExpr Γ τ) → ArithExpr Γ τ
  mul       : List⁺ (ArithExpr Γ τ) → ArithExpr Γ τ

----------------------------
-- Comparison expressions

data CompExpr (Γ : NetworkDeclarations) (τ : ElementType) : Set where
  greaterThan  : ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ
  lessThan     : ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ
  greaterEqual : ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ
  lessEqual    : ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ
  notEqual     : ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ
  equal        : ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ

-------------------------
-- Boolean expressions

data BoolExpr (Γ : NetworkDeclarations) : Set where
  literal    : Bool → BoolExpr Γ
  comparison : ∀ {τ} → CompExpr Γ τ → BoolExpr Γ
  and        : List⁺ (BoolExpr Γ) → BoolExpr Γ
  or         : List⁺ (BoolExpr Γ) → BoolExpr Γ

----------------
-- Assertions

data Assertion (Γ : NetworkDeclarations) : Set where
  assert : BoolExpr Γ → Assertion Γ

-------------
-- Queries --
-------------

record Query : Set where
  constructor query
  field
    networks : NetworkDeclarations
    assertions : List (Assertion networks)

    -- Additional proof that the equivalences inside the network declarations are valid
    equivalences : ValidNetworkEquivalences networks

open Query public

----------------------
-- Runtime networks --
----------------------

private
  variable
    Γ : NetworkDeclarations
    d d₁ d₂ : NetworkDeclaration
    γ : NetworkType ElementType

-----------------------------
-- Network implementations

CorrespondingHiddenNode : ∀ {γ} → Model γ → HiddenDeclaration → Set
CorrespondingHiddenNode model h = NodeOutput model (nodeOutputName h) (hiddenType h)

record NetworkImplementation (d : NetworkDeclaration) : Set where
  constructor networkImplementation
  field
    model             : Model (typeOfNetwork d)
    hiddenNodeMapping : All (CorrespondingHiddenNode model) (hiddenDeclarations d)

open NetworkImplementation

NetworkImplementations : NetworkDeclarations → Set
NetworkImplementations = All NetworkImplementation

-----------------------------
-- Network implementations respect

ModelsEqual : ∀ {name} → NetworkImplementation d₁ → (NetworkImplementation d₂ × ValidEqualToTarget name d₁ d₂) → Set
ModelsEqual current (target , targetValid) = model current ≡[ targetTypesMatch targetValid ] model target
  where open ValidEqualToTarget

ModelsIsomorphic : ∀ {name} → NetworkImplementation d₁ → (NetworkImplementation d₂ × ValidIsomorphicToTarget name d₁ d₂) → Set
ModelsIsomorphic current (target , targetValid) = model current ↭[ targetShapesMatch targetValid ] model target
  where open ValidIsomorphicToTarget

ModelsEquivalent : NetworkImplementations Γ → NetworkImplementation d → ∀ {e} → ValidNetworkEquivalence Γ d e → Set
ModelsEquivalent models i none                       = ⊤
ModelsEquivalent models i (equal-to networkVar)      = ModelsEqual i (lookupAny models networkVar)
ModelsEquivalent models i (isomorphic-to networkVar) = ModelsIsomorphic i (lookupAny models networkVar)

data ImplementationsRespectsEquivalences : ∀ {Γ} → ValidNetworkEquivalences Γ → NetworkImplementations Γ → Set where
  [] : ImplementationsRespectsEquivalences [] []
  _∷_ : ∀ {e : ValidNetworkEquivalence Γ d (equivalence d)}
           {es : ValidNetworkEquivalences Γ}
           {i : NetworkImplementation d}
           {is : NetworkImplementations Γ} →
           ModelsEquivalent is i e →
           ImplementationsRespectsEquivalences es is →
           ImplementationsRespectsEquivalences (e ∷ es) (i ∷ is)

----------------------------------------------
-- Network implementations for a given query

record QueryModels (q : Query) : Set where
  constructor queryModels
  field
    networkImplementations : NetworkImplementations (networks q)
    implementationsRespectEquivalences : ImplementationsRespectsEquivalences (equivalences q) networkImplementations

-----------------------
-- Input assignments --
-----------------------

InputAssignment : NetworkPredicate
InputAssignment d = All⁺ TheoryTensor (typeOfInputs d)

InputAssignments : NetworkDeclarations → Set
InputAssignments ds = All InputAssignment ds
