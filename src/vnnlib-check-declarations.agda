module vnnlib-check-declarations where

open import Data.List as List
open import Data.List.Properties using (length-map)
open import Data.List.NonEmpty as List⁺
open import Data.Bool as Bool
open import Data.String as String using (String; _==_)
open import Relation.Binary.PropositionalEquality
open import Data.Fin as Fin
open import Data.Nat as ℕ
open import vnnlib-syntax as 𝐕
open import Syntax.AST as 𝐁 hiding (String)
open import Data.List.Relation.Unary.Any as RUAny
open import Relation.Nullary
open import Data.Nat.Show
open import Data.Maybe using (Maybe;just;nothing)

open import tensor as 𝐓 using (TensorShape)
open import syntax-utils
open import utils
open import vnnlib-types as 𝐄

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

-- convert a list of numbers to valid tensor shape
parseNumbersList : List 𝐁.Number → Result (List ℕ)
parseNumbersList [] = success []
parseNumbersList (x ∷ n) = do
  x' ← convertMaybeToResult (readMaybe 10 ⟦ x ⟧asStringₙ)
  n' ← parseNumbersList n
  return (x' ∷ n')

convertTensorShape : 𝐁.TensorShape → Result (List ℕ)
convertTensorShape scalarDims = success []
convertTensorShape (tensorDims xs) = parseNumbersList xs

convertElementType : 𝐁.ElementType → Result 𝐄.ElementType
convertElementType genericElementType = success real
convertElementType elementTypeF16 = success float16
convertElementType elementTypeF32 = success float32
convertElementType elementTypeF64 = success float64
convertElementType elementTypeBF16 = success bfloat16 
convertElementType elementTypeF8E4M3FN = success float8e4m3fn
convertElementType elementTypeF8E5M2 = success float8e5m2 
convertElementType elementTypeF8E4M3FNUZ = success float8e4m3fnuz
convertElementType elementTypeF8E5M2FNUZ = success float8e5m2fnuz
convertElementType elementTypeF4E2M1 = success float4e2m1
convertElementType elementTypeI8 = success int8
convertElementType elementTypeI16 = success int16
convertElementType elementTypeI32 = success int32
convertElementType elementTypeI64 = success int64
convertElementType elementTypeU8 = success uint8
convertElementType elementTypeU16 = success uint16
convertElementType elementTypeU32 = success uint32
convertElementType elementTypeU64 = success uint64
convertElementType elementTypeC64 = error "complex64 not supported"
convertElementType elementTypeC128 = error "complex128 not supported"
convertElementType elementTypeBool = error "boolType not supported"
convertElementType elementTypeString = error "stringType not supported"

convertInputDefinition : 𝐁.InputDefinition → Result (𝐕.InputDefinition)
convertInputDefinition (inputDef x e t) = do
  t' ← convertTensorShape t
  e' ← convertElementType e
  return (declareInput (SVariableName ⟦ x ⟧asString) e' t')
convertInputDefinition (inputOnnxDef x₁ e t x₂) = do
  t' ← convertTensorShape t
  e' ← convertElementType e
  return (declareInput (SVariableName ⟦ x₁ ⟧asString) e' t')

-- convertHiddenDefinition : 𝐁.HiddenDefinition → 𝐕.HiddenDefinition

convertOutputDefinition : 𝐁.OutputDefinition → Result 𝐕.OutputDefinition
convertOutputDefinition (outputDef x e t) = do
  t' ← (convertTensorShape t)
  e' ← convertElementType e
  return (declareOutput (SVariableName ⟦ x ⟧asString) e' t')
convertOutputDefinition (outputOnnxDef x₁ e t x₂) = do
  t' ←  (convertTensorShape t)
  e' ← convertElementType e
  return (declareOutput (SVariableName ⟦ x₁ ⟧asString) e' t')

-- get DeBrujin's index from context
isResultSuccess : {A : Set} → Result A → Bool
isResultSuccess (error _) = false
isResultSuccess (success _) = true

getInputIndex : 𝐕.VariableName → (is : List 𝐕.InputDefinition) →  Result (Fin (List.length is))
getInputIndex v is with any? (λ x → ⟦ v ⟧asStringᵥ  String.≟  ⟦ getInputName x ⟧asStringᵥ ) is
... | yes p = success (index p)
... | no ¬p = error "Input name not in network definition"

getOutputIndex : 𝐕.VariableName → (os : List 𝐕.OutputDefinition) → Result (Fin (List.length os))
getOutputIndex v os with any? (λ x → ⟦ v ⟧asStringᵥ  String.≟  ⟦ getOutputName x ⟧asStringᵥ ) os
... | yes p = success (index p)
... | no ¬p = error "Output name not in network definition"

checkNetworkIndex : 𝐕.VariableName → 𝐕.NetworkDefinition → Result (Bool) -- the Bool is placeholder type
checkNetworkIndex varName n with getInputIndex varName (getInputDefs n) | getOutputIndex varName (getOutputDefs n)
... | error x | error x₁ = error "Variable name not found"
... | error x | success y = success true
... | success y | error x = success true
... | success y | success y₁ = error "Variable name not unique" -- should be unreachable

getNetworkIndex : (ns : List 𝐕.NetworkDefinition) → 𝐕.VariableName → Result (Fin (List.length ns))
getNetworkIndex ns v with any? (λ x → isResultSuccess x Bool.≟ true ) (List.map (checkNetworkIndex v) ns)
... | yes p = success (cast equal-length (index p))
  where
    equal-length : List.length (List.map (checkNetworkIndex v) ns) ≡ List.length ns
    equal-length = length-map (checkNetworkIndex v) ns
... | no ¬p = error "Network with variable does not exist"

-- Scope checking inputs and outputs
mkNetworkInputs : List 𝐕.NetworkDefinition → List 𝐁.InputDefinition → Result (List 𝐕.InputDefinition)
mkNetworkInputs Γ is = List.foldl addInputVar (success []) is
  where    
    addInputVar : Result (List 𝐕.InputDefinition) → 𝐁.InputDefinition → Result (List 𝐕.InputDefinition)
    addInputVar (error e) i = error e
    addInputVar (success is') i = do
      i' ← convertInputDefinition i
      let v = getInputName i'
      if (isResultSuccess (getNetworkIndex Γ v) ∨ isResultSuccess (getInputIndex v is')) then error "Variable Names must be unique" else success (i' ∷ is')

------------- Add network outputs ----------------
mkNetworkOutputs : List 𝐕.NetworkDefinition → List 𝐕.InputDefinition → List 𝐁.OutputDefinition → Result (List 𝐕.OutputDefinition)
mkNetworkOutputs Γ defsᵢ os = List.foldl addOutputVar (success []) os
  where    
    addOutputVar : Result (List 𝐕.OutputDefinition) → 𝐁.OutputDefinition → Result (List 𝐕.OutputDefinition)
    addOutputVar (error e) o = error e
    addOutputVar (success os') o = do
      o' ← convertOutputDefinition o
      let v = getOutputName o'
      if (isResultSuccess (getNetworkIndex Γ v) ∨ isResultSuccess (getInputIndex v defsᵢ) ∨ isResultSuccess (getOutputIndex v os')) then error "Variable Names must be unique" else success (o' ∷ os')

mkNetworkDefinition : List 𝐕.NetworkDefinition → 𝐁.NetworkDefinition → Result (𝐕.NetworkDefinition)
mkNetworkDefinition ns n with convertListToList⁺ (getHiddenDefsᵇ n)
... | success _ = error "Hidden Definitions not supported"
... | error _ with convertListToList⁺ (getInputDefsᵇ n) | convertListToList⁺ (getOutputDefsᵇ n)
... | error _ | error _ = error "Network Definitions must have inputs and outputs"
... | error _ | success y = error "Network Definitions must have inputs"
... | success _ | error _ = error "Network Definitions must have outputs"
... | success is | success os = do
      is' ← mkNetworkInputs ns (toList is)
      os' ← mkNetworkOutputs ns is' (toList os)
      return (declareNetwork (convertVariableName (getNetworkNameᵇ n)) is' os')

-- Returns the index of the network Definition that the congruence statement points to
refOfCompStm : (ns : List 𝐕.NetworkDefinition) → List 𝐁.CompStm → Maybe (Result (Fin (List.length ns)))
refOfCompStm ns [] = nothing
refOfCompStm ns (c ∷ tail₁) with tail₁
... | x ∷ a = just (error "There can only be 1 congruence statement per network declaration")
... | [] with any? (λ n → ⟦ getCompStmName c ⟧asString String.≟ ⟦ getNetworkName n ⟧asStringᵥ) ns
... | no ¬p = just (error "Congruence Statements must refer to defined networks")
... | yes p = just (success (index p))

parseNetworkDef : Result (List 𝐕.NetworkDefinition) → 𝐁.NetworkDefinition → Result (List 𝐕.NetworkDefinition)
parseNetworkDef (error x) n = error x
parseNetworkDef (success ns) n with any? (λ x → ⟦ getNetworkNameᵇ n ⟧asString String.≟ ⟦ getNetworkName x ⟧asStringᵥ) ns
... | yes p = error "Networks cannot have duplicate names"
... | no ¬p with refOfCompStm ns (getCompStms n)
... | just csRef = error "Congruence Statements not supported"
... | nothing = do
        n' ← mkNetworkDefinition ns n
        return ( n' ∷ ns )

------------ Create the Check context -----------
mkCheckContext : List 𝐁.NetworkDefinition → Result (List 𝐕.NetworkDefinition)
mkCheckContext networkDefs = do
  ns' ← List.foldl parseNetworkDef (success []) networkDefs
  return ns'
