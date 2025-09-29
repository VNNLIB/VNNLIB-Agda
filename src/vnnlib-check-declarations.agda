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
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Function using (_∘_)

open import tensor as 𝐓 using (TensorShape)
open import syntax-utils
open import types-utils
open import vnnlib-types as 𝐄

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

-- Context for both scope and type checking
data VariableBinding : Set where
  var : 𝐕.VariableName → 𝐓.TensorShape → 𝐄.ElementType → VariableBinding

getVariableNameⱽ : VariableBinding → 𝐕.VariableName
getVariableNameⱽ (var x x₁ x₂) = x

getTensorShape : VariableBinding → 𝐓.TensorShape
getTensorShape (var x x₁ x₂) = x₁

getElementType : VariableBinding → 𝐄.ElementType
getElementType (var x x₁ x₂) = x₂

fromVariableBindingᵢ : VariableBinding → 𝐕.InputDefinition
fromVariableBindingᵢ (var x x₁ x₂) = declareInput x x₂ x₁

fromVariableBindingₒ : VariableBinding → 𝐕.OutputDefinition
fromVariableBindingₒ (var x x₁ x₂) = declareOutput x x₂ x₁

toVariableBindingᵢ : 𝐕.InputDefinition → VariableBinding
toVariableBindingᵢ (declareInput x x₁ x₂) = var x x₂ x₁

toVariableBindingₒ : 𝐕.OutputDefinition → VariableBinding
toVariableBindingₒ (declareOutput x x₁ x₂) = var x x₂ x₁

record NetworkBinding : Set where
  constructor
    networkBinding
  field
    inputs : List VariableBinding
    outputs : List VariableBinding

CheckContextPair : Set
CheckContextPair = NetworkBinding × 𝐕.NetworkDefinition

CheckContext : Set
CheckContext = List (CheckContextPair)

convertNetworkBindingToDef : 𝐕.VariableName → NetworkBinding → 𝐕.NetworkDefinition
convertNetworkBindingToDef networkName (networkBinding inputs₁ outputs₁) = declareNetwork networkName (List.map fromVariableBindingᵢ inputs₁) (List.map fromVariableBindingₒ (outputs₁))


-- get DeBrujin's index from context
open NetworkBinding

variableIndexInNetworkᵢₙₚᵤₜ : (n : NetworkBinding) → (varName : 𝐕.VariableName) → Result (Fin (List.length (inputs n)))
variableIndexInNetworkᵢₙₚᵤₜ Ν name with any? (λ x → ⟦ name ⟧asStringᵥ String.≟ ⟦ getVariableNameⱽ x ⟧asStringᵥ) ((inputs Ν))
... | yes p = success (index p)
... | no ¬p = error "Variable Name not in inputs"

variableIndexInNetworkₒᵤₜₚᵤₜ : (n : NetworkBinding) → (varName : 𝐕.VariableName) → Result (Fin (List.length ((outputs n))))
variableIndexInNetworkₒᵤₜₚᵤₜ Ν name with any? (λ x → ⟦ name ⟧asStringᵥ String.≟ ⟦ getVariableNameⱽ x ⟧asStringᵥ) ((outputs Ν))
... | yes p = success (index p)
... | no ¬p = error "Variable Input Name must be unique"

-- the network index is derived if the variable is in its inputs or outputs
checkNetworkIndex : (varName : 𝐕.VariableName) → (n : NetworkBinding) → Result Bool -- the Bool is placeholder enum type
checkNetworkIndex varName Ν with variableIndexInNetworkᵢₙₚᵤₜ Ν varName
... | success x = success (true)
... | error _ with variableIndexInNetworkₒᵤₜₚᵤₜ Ν varName
... | success x = success (true)
... | error _ = error "Variable Name in network Binding not unique"

isResultSuccess : Result Bool → Bool
isResultSuccess (error _) = false
isResultSuccess (success _) = true

getNetworkBindings : CheckContext → List NetworkBinding
getNetworkBindings Γ = List.map proj₁ Γ

variableNetworkIndex : (varName : 𝐕.VariableName) → (l : CheckContext) → Result (Fin (List.length l))
variableNetworkIndex varName Γ with any? (λ x → isResultSuccess x Bool.≟ true) (List.map (checkNetworkIndex varName ∘ proj₁) Γ)
... | yes p = success (subst Fin equal-length (index p))
  where
    equal-length : List.length (List.map (checkNetworkIndex varName ∘ proj₁) Γ) ≡ List.length Γ
    equal-length = length-map (checkNetworkIndex varName ∘ proj₁) Γ
... | no ¬p = error "Variable not found in network context"

isVariableNameInVariableBinding : 𝐕.VariableName → List VariableBinding → Bool
isVariableNameInVariableBinding varName vars with any? (λ x → ⟦ varName ⟧asStringᵥ String.≟ ⟦ getVariableNameⱽ x ⟧asStringᵥ) vars
... | yes _ = true
... | no _ = false


-- Check the current context and interatively built Variable Binding to determine if the adding variable name is unique
isVariableNameUnique : 𝐕.VariableName → CheckContext → List VariableBinding → Bool
isVariableNameUnique varName Γ vars with variableNetworkIndex varName Γ 
... | error x = not (isVariableNameInVariableBinding varName vars)
... | success y = false


-- Scope checking inputs and outputs
mkNetworkInputs : CheckContext → List 𝐕.InputDefinition → Result (List VariableBinding)
mkNetworkInputs Γ is = List.foldl addInputVarₙ (success []) is
  where    
    addInputVarₙ : Result (List VariableBinding) → 𝐕.InputDefinition → Result (List VariableBinding)
    addInputVarₙ (error e) i = error e
    addInputVarₙ (success varsᵢ) i =
      let varName = inputVarsᵥ i in if isVariableNameUnique varName Γ varsᵢ then success (toVariableBindingᵢ i ∷ varsᵢ) else error "Variable Names must be unique"

------------- Add network outputs ----------------
mkNetworkOutputs : CheckContext → List VariableBinding → List 𝐕.OutputDefinition → Result (List VariableBinding)
mkNetworkOutputs Γ varsᵢ os = List.foldl addOutputVarₙ (success []) os
  where    
    addOutputVarₙ : Result (List VariableBinding) → 𝐕.OutputDefinition → Result (List VariableBinding)
    addOutputVarₙ (error e) _ = error e
    addOutputVarₙ (success varsₒ) o =
      let varName = (outputVarsᵥ o) in if isVariableNameUnique varName Γ varsᵢ ∧ isVariableNameUnique varName Γ varsₒ
      then success (toVariableBindingₒ o ∷ varsₒ) else error "Variable Names must be unique"

mkNetworkContextₙ : CheckContext → List 𝐕.InputDefinition → List 𝐕.OutputDefinition → Result (NetworkBinding)
mkNetworkContextₙ Γ is os = do
  is' ← mkNetworkInputs Γ is
  os' ← mkNetworkOutputs Γ is' os
  return (networkBinding is' os')

------------ Create the Check context -----------
mkCheckContext : List 𝐁.NetworkDefinition → Result CheckContext
mkCheckContext networkDefs with convertNetworkDefs networkDefs
... | error x = error x
... | success ns = List.foldl networkₙ (success []) ns
  where
    networkₙ : Result CheckContext → 𝐕.NetworkDefinition → Result CheckContext
    networkₙ (error x) n = error x
    networkₙ (success Γ) n = do
      n' ← mkNetworkContextₙ Γ (getInputDefsᵥ n) (getOutputDefsᵥ n)
      return ((n' , n) ∷ Γ)
