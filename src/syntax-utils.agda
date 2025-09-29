module syntax-utils where

open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.String as String hiding (toList)
open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import Data.Nat as ℕ
open import Data.Bool
open import Data.Integer as ℤ using (∣_∣)
open import vnnlib-types as 𝐄
open import Data.Maybe using (Maybe)
open import Data.Nat.Show
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import types-utils

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ variableName (#pair pos name) ⟧asString = name

⟦_⟧asStringᵥ : 𝐕.VariableName → String
⟦ (SVariableName name) ⟧asStringᵥ = name

⟦_⟧asStringₙ : 𝐁.Number → String
⟦ number (#pair pos name) ⟧asStringₙ = name

postulate parseNumber : (τ : 𝐄.ElementType) → 𝐁.Number → Maybe (𝐄.ElementTypeToSet τ)

convertElementType : 𝐁.ElementType → 𝐄.ElementType
convertElementType genericElementType = real
convertElementType elementTypeF16 = float16
convertElementType elementTypeF32 = float32
convertElementType elementTypeF64 = float64
convertElementType elementTypeBF16 = bfloat16 
convertElementType elementTypeF8E4M3FN = float8e4m3fn
convertElementType elementTypeF8E5M2 = float8e5m2 
convertElementType elementTypeF8E4M3FNUZ = float8e4m3fnuz
convertElementType elementTypeF8E5M2FNUZ = float8e5m2fnuz
convertElementType elementTypeF4E2M1 = float4e2m1
convertElementType elementTypeI8 = int8
convertElementType elementTypeI16 = int16
convertElementType elementTypeI32 = int32
convertElementType elementTypeI64 = int64
convertElementType elementTypeU8 = uint8
convertElementType elementTypeU16 = uint16
convertElementType elementTypeU32 = uint32
convertElementType elementTypeU64 = uint64
convertElementType elementTypeC64 = complex64
convertElementType elementTypeC128 = complex128
convertElementType elementTypeBool = boolType
convertElementType elementTypeString = stringType

convertVariableName : 𝐁.VariableName → 𝐕.VariableName
convertVariableName (variableName (#pair x x₁)) = SVariableName x₁

-- Get variable Names
inputVarsᵥ : 𝐕.InputDefinition → 𝐕.VariableName
inputVarsᵥ (declareInput x _ _) = x

hiddenVars : 𝐁.HiddenDefinition → 𝐁.VariableName
hiddenVars (hiddenDef x₁ e t x₂) = x₁

outputVars : 𝐁.OutputDefinition → 𝐁.VariableName
outputVars (outputDef x e t) = x
outputVars (outputOnnxDef x₁ e t x₂) = x₁

outputVarsᵥ : 𝐕.OutputDefinition → 𝐕.VariableName
outputVarsᵥ (declareOutput x _ _) = x

getCompStms : 𝐁.NetworkDefinition → List 𝐁.CompStm
getCompStms (networkDef _ cs _ _ _) = cs

getCompStmName : 𝐁.CompStm → 𝐁.VariableName
getCompStmName (isomorphicTo x) = x
getCompStmName (equalTo x) = x

getInputDefs : 𝐁.NetworkDefinition → List 𝐁.InputDefinition
getInputDefs (networkDef _ _ is _ _) = is

getInputDefsᵥ : 𝐕.NetworkDefinition → List 𝐕.InputDefinition
getInputDefsᵥ (declareNetwork _ is _) = is

getOutputDefs : 𝐁.NetworkDefinition → List 𝐁.OutputDefinition
getOutputDefs (networkDef _ _ _ _ os) = os

getOutputDefsᵥ : 𝐕.NetworkDefinition → List 𝐕.OutputDefinition
getOutputDefsᵥ (declareNetwork _ _ os) = os

getNetworkName : 𝐁.NetworkDefinition → 𝐁.VariableName
getNetworkName (networkDef x _ _ _ _) = x

getNetworkNameᵥ : 𝐕.NetworkDefinition → 𝐕.VariableName
getNetworkNameᵥ (declareNetwork x _ _) = x


inclNetworkDefsCompStm : 𝐁.NetworkDefinition → Bool
inclNetworkDefsCompStm (networkDef _ cs _ _ _) = 1 ≤ᵇ List.length cs

inclNetworkDefsHiddenDefs : 𝐁.NetworkDefinition → Bool
inclNetworkDefsHiddenDefs (networkDef _ _ _ hs _) = 1 ≤ᵇ List.length hs


-- convert a list of number to valid numbers
parseNumbersList : List 𝐁.Number → Result (List ℕ)
parseNumbersList [] = success []
parseNumbersList (x ∷ n) = do
  x' ← convertMaybeToResult (readMaybe 10 ⟦ x ⟧asStringₙ)
  n' ← parseNumbersList n
  return (x' ∷ n')

convertTensorShape : 𝐁.TensorShape → Result (List ℕ)
convertTensorShape scalarDims = success []
convertTensorShape (tensorDims xs) = parseNumbersList xs

convertInputDefinition : 𝐁.InputDefinition → Result (𝐕.InputDefinition)
convertInputDefinition (inputDef x e t) = do
  t' ← convertTensorShape t
  return (declareInput (SVariableName ⟦ x ⟧asString) (convertElementType e) t')
convertInputDefinition (inputOnnxDef x₁ e t x₂) = do
  t' ← convertTensorShape t
  return (declareInput (SVariableName ⟦ x₁ ⟧asString) (convertElementType e) t')

-- convertHiddenDefinition : 𝐁.HiddenDefinition → 𝐕.HiddenDefinition

convertOutputDefinition : 𝐁.OutputDefinition → Result 𝐕.OutputDefinition
convertOutputDefinition (outputDef x e t) = do
  t' ← (convertTensorShape t)
  return (declareOutput (SVariableName ⟦ x ⟧asString) (convertElementType e) t')
convertOutputDefinition (outputOnnxDef x₁ e t x₂) = do
  t' ←  (convertTensorShape t)
  return (declareOutput (SVariableName ⟦ x₁ ⟧asString) (convertElementType e) t')

appendInputs : Result (List 𝐕.InputDefinition) →  𝐁.InputDefinition → Result (List 𝐕.InputDefinition)
appendInputs is i = do
  i' ← convertInputDefinition i
  is' ← is
  return (i' ∷ is')

appendOutputs : Result (List 𝐕.OutputDefinition) → 𝐁.OutputDefinition → Result (List 𝐕.OutputDefinition)
appendOutputs os o = do
  o' ← convertOutputDefinition o
  os' ← os
  return (o' ∷ os')

convertNetworkDefinition : 𝐁.NetworkDefinition → Result (𝐕.NetworkDefinition)
convertNetworkDefinition (networkDef x _ is _ os) with convertListToList⁺ is | convertListToList⁺ os
... | error _ | error _ = error "Network Definitions must have inputs and outputs"
... | error _ | success y = error "Network Definitions must have inputs"
... | success y | error _ = error "Network Definitions must have outputs"
... | success y | success y₁ = do
      is' ← List.foldl appendInputs (success []) is
      os' ← List.foldl appendOutputs (success []) os
      return (declareNetwork (convertVariableName x) is' os')

isDefinedNetworkName : List 𝐕.NetworkDefinition → List 𝐁.CompStm → Bool
isDefinedNetworkName ns [] = true
isDefinedNetworkName ns (x ∷ xs) with any? (λ n → ⟦ getCompStmName x ⟧asString String.≟ ⟦ getNetworkNameᵥ n ⟧asStringᵥ) ns
... | no ¬p = isDefinedNetworkName ns xs
... | yes p = true

appendNetworks : Result (List 𝐕.NetworkDefinition) → 𝐁.NetworkDefinition → Result (List 𝐕.NetworkDefinition)
appendNetworks (error x) n = error x
appendNetworks (success ns) n with any? (λ x → ⟦ getNetworkName n ⟧asString String.≟ ⟦ getNetworkNameᵥ x ⟧asStringᵥ) ns
... | yes p = error "Networks cannot have duplicate names"
... | no ¬p = if isDefinedNetworkName ns (getCompStms n)
              then (do
                n' ← convertNetworkDefinition n
                return ( n' ∷ ns ))
              else error "Undefined Network name used"

convertNetworkDefs : List 𝐁.NetworkDefinition → Result (List 𝐕.NetworkDefinition)
convertNetworkDefs networkDefs = do
  ns' ← List.foldl appendNetworks (success []) networkDefs
  return ns'
