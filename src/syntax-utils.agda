module syntax-utils where

open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.String as String hiding (toList)
open import Data.Nat as ℕ
open import Data.Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.Maybe using (Maybe;nothing;just)

open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import vnnlib-types as 𝐄
open import utils
open import tensor as 𝐓

-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ variableName (#pair pos name) ⟧asString = name

⟦_⟧asStringᵥ : 𝐕.VariableName → String
⟦ (SVariableName name) ⟧asStringᵥ = name

⟦_⟧asStringₙ : 𝐁.Number → String
⟦ number (#pair pos name) ⟧asStringₙ = name

convertVariableName : 𝐁.VariableName → 𝐕.VariableName
convertVariableName (variableName (#pair x x₁)) = SVariableName x₁

postulate parseNumber : (τ : 𝐄.ElementType) → 𝐁.Number → Maybe (ElementTypeToSet τ)

-- Get variable Names
getInputName : 𝐕.InputDefinition → 𝐕.VariableName
getInputName (declareInput x _ _) = x

getHiddenNameᵇ : 𝐁.HiddenDefinition → 𝐁.VariableName
getHiddenNameᵇ (hiddenDef x₁ e t x₂) = x₁

getOutputNameᵇ : 𝐁.OutputDefinition → 𝐁.VariableName
getOutputNameᵇ (outputDef x e t) = x
getOutputNameᵇ (outputOnnxDef x₁ e t x₂) = x₁

getOutputName : 𝐕.OutputDefinition → 𝐕.VariableName
getOutputName (declareOutput x _ _) = x

getCompStms : 𝐁.NetworkDefinition → Maybe 𝐁.CompStm
getCompStms (networkDef x is hs os) = nothing
getCompStms (networkDefCompStm x c is hs os) = just c

getCompStmName : 𝐁.CompStm → 𝐁.VariableName
getCompStmName (isomorphicTo x) = x
getCompStmName (equalTo x) = x

getInputDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.InputDefinition
getInputDefsᵇ (networkDef x is hs os) = is
getInputDefsᵇ (networkDefCompStm x c is hs os) = is

getOutputDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.OutputDefinition
getOutputDefsᵇ (networkDef x is hs os) = os
getOutputDefsᵇ (networkDefCompStm x c is hs os) = os

getNetworkNameᵇ : 𝐁.NetworkDefinition → 𝐁.VariableName
getNetworkNameᵇ (networkDef x is hs os) = x
getNetworkNameᵇ (networkDefCompStm x c is hs os) = x

getNetworkName : 𝐕.NetworkDefinition → 𝐕.VariableName
getNetworkName (declareNetwork x _ _) = x

getElementTypeᵢ : 𝐕.InputDefinition → 𝐄.ElementType
getElementTypeᵢ (declareInput x x₁ x₂) = x₁

getElementTypeₒ : 𝐕.OutputDefinition → 𝐄.ElementType
getElementTypeₒ (declareOutput x x₁ x₂) = x₁

getInputShape : 𝐕.InputDefinition → 𝐓.TensorShape
getInputShape (declareInput x x₁ x₂) = x₂

getOutputShape : 𝐕.OutputDefinition → 𝐓.TensorShape
getOutputShape (declareOutput x x₁ x₂) = x₂

getHiddenDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.HiddenDefinition
getHiddenDefsᵇ (networkDef x is hs os) = hs
getHiddenDefsᵇ (networkDefCompStm x c is hs os) = hs

inclNetworkDefsHiddenDefs : 𝐁.NetworkDefinition → Bool
inclNetworkDefsHiddenDefs n = let hs = (getHiddenDefsᵇ n) in 1 ≤ᵇ List.length hs
