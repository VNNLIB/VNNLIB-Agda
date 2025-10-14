
module vnnlib-syntax where

open import Data.List as List using (List; map)
open import Data.String using (String)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Bool using (Bool)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List.Membership.Propositional using (_∈_)

open import vnnlib-types using (ElementType; ElementTypeToSet)
open import tensor using (TensorShape; TensorIndices)

-- Variables
--  -- Naming/referencing
data VariableName : Set where
  SVariableName : String → VariableName

-- Declarations are used to contruct the context
-- -- Each entry in the context is a network type
record NetworkType : Set where
  constructor
    networkType
  field
    inputShapes&Types : List (TensorShape × ElementType )
    outputShapes&Types : List (TensorShape × ElementType )


-- Node Definitions
data InputDefinition : Set where
  declareInput : VariableName → ElementType → TensorShape → InputDefinition

-- data IntermediateDefinition : Set where
  -- declareIntermediate : VariableName → ElementType → TensorShape → String → IntermediateDefinition

data OutputDefinition : Set where
  declareOutput : VariableName → ElementType → TensorShape → OutputDefinition

-- Network Definitions
data NetworkDefinition : Set where
  declareNetwork : VariableName → List InputDefinition → List OutputDefinition → NetworkDefinition

-- Context is a list of network types
Context : Set
Context = List (NetworkType)

getOutputDefs : NetworkDefinition → List OutputDefinition
getOutputDefs (declareNetwork _ _ os) = os

getInputDefs : NetworkDefinition → List InputDefinition
getInputDefs (declareNetwork _ is _) = is

convertInputΓ : InputDefinition → TensorShape × ElementType
convertInputΓ (declareInput _ e₂ x₂) = x₂ , e₂

convertOutputΓ : OutputDefinition → TensorShape × ElementType
convertOutputΓ (declareOutput _ e₂ x₂) = x₂ , e₂

convertNetworkΓ : NetworkDefinition → NetworkType
convertNetworkΓ n = networkType (List.map convertInputΓ (getInputDefs n)) (List.map convertOutputΓ (getOutputDefs n))

-- Network definitions are used to create the context
mkContext : List NetworkDefinition → Context
mkContext networkDefinitions = List.map convertNetworkΓ networkDefinitions 


-- Assertions
module _ (Γ : Context) where
  NetworkRef : Set
  NetworkRef = Fin (List.length Γ)

  InputRef : NetworkRef → ElementType → TensorShape → Set
  InputRef netRef τ s = (s , τ) ∈ (NetworkType.inputShapes&Types (List.lookup Γ netRef))

  OutputRef : NetworkRef → ElementType → TensorShape → Set
  OutputRef netRef τ s = (s , τ) ∈ (NetworkType.outputShapes&Types (List.lookup Γ netRef))

  -- Arithmetic Expressions
  data ArithExpr (τ : ElementType) : Set where
    constant : ElementTypeToSet τ → ArithExpr τ
    negate : ArithExpr τ → ArithExpr τ 
    varInput : {shape : TensorShape} (i : NetworkRef) (j : InputRef i τ shape) → TensorIndices shape → ArithExpr τ
    varOutput : {shape : TensorShape} (i : NetworkRef) (j : OutputRef i τ shape) → TensorIndices shape → ArithExpr τ
    add : List (ArithExpr τ) → ArithExpr τ
    minus : List (ArithExpr τ) → ArithExpr τ
    mult  : List (ArithExpr τ) → ArithExpr τ

  -- Comparative Expressions : 2-ary operations
  data CompExpr (τ : ElementType) : Set where
    greaterThan    : ArithExpr τ → ArithExpr τ → CompExpr τ
    lessThan       : ArithExpr τ → ArithExpr τ → CompExpr τ
    greaterEqual   : ArithExpr τ → ArithExpr τ → CompExpr τ
    lessEqual      : ArithExpr τ → ArithExpr τ → CompExpr τ
    notEqual       : ArithExpr τ → ArithExpr τ → CompExpr τ
    equal          : ArithExpr τ → ArithExpr τ → CompExpr τ

  -- Boolean Expressions: Connective and Comparative Expressions
  data BoolExpr : Set where
    literal : Bool → BoolExpr
    compExpr : Σ ElementType CompExpr → BoolExpr
    andExpr : List BoolExpr → BoolExpr
    orExpr  : List BoolExpr → BoolExpr

  -- Assertions : evalute to true or false
  data Assertion : Set where
    assert : BoolExpr → Assertion

-- Query
data Query : Set where
  mkQuery : (networks : List NetworkDefinition) → List (Assertion (mkContext networks)) → Query
