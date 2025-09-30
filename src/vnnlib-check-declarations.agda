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
mkNetworkDefinition ns (networkDef x _ is _ os) with convertListToList⁺ is | convertListToList⁺ os
... | error _ | error _ = error "Network Definitions must have inputs and outputs"
... | error _ | success y = error "Network Definitions must have inputs"
... | success y | error _ = error "Network Definitions must have outputs"
... | success y | success y₁ = do
      is' ← mkNetworkInputs ns is
      os' ← mkNetworkOutputs ns is' os
      return (declareNetwork (convertVariableName x) is' os')

isDefinedNetworkName : List 𝐕.NetworkDefinition → List 𝐁.CompStm → Bool
isDefinedNetworkName ns [] = true
isDefinedNetworkName ns (x ∷ xs) with any? (λ n → ⟦ getCompStmName x ⟧asString String.≟ ⟦ getNetworkName n ⟧asStringᵥ) ns
... | no ¬p = isDefinedNetworkName ns xs
... | yes p = true

parseNetworkDef : Result (List 𝐕.NetworkDefinition) → 𝐁.NetworkDefinition → Result (List 𝐕.NetworkDefinition)
parseNetworkDef (error x) n = error x
parseNetworkDef (success ns) n with any? (λ x → ⟦ getNetworkNameᵇ n ⟧asString String.≟ ⟦ getNetworkName x ⟧asStringᵥ) ns
... | yes p = error "Networks cannot have duplicate names"
... | no ¬p = if isDefinedNetworkName ns (getCompStms n)
              then (do
                n' ← mkNetworkDefinition ns n
                return ( n' ∷ ns ))
              else error "Undefined Network name used"

------------ Create the Check context -----------
mkCheckContext : List 𝐁.NetworkDefinition → Result (List 𝐕.NetworkDefinition)
mkCheckContext networkDefs = do
  ns' ← List.foldl parseNetworkDef (success []) networkDefs
  return ns'
