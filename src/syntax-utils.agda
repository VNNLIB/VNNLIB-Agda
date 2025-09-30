module syntax-utils where

open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.String as String hiding (toList)
open import Data.Nat as ℕ
open import Data.Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.Maybe using (Maybe)

open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-syntax as 𝐕
open import vnnlib-types as 𝐄
open import types-utils
open import tensor as 𝐓

-- convert the BNFC VariableName to agda string type
⟦_⟧asString : 𝐁.VariableName → String
⟦ variableName (#pair pos name) ⟧asString = name

⟦_⟧asStringᵥ : 𝐕.VariableName → String
⟦ (SVariableName name) ⟧asStringᵥ = name

⟦_⟧asStringₙ : 𝐁.Number → String
⟦ number (#pair pos name) ⟧asStringₙ = name

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

getCompStms : 𝐁.NetworkDefinition → List 𝐁.CompStm
getCompStms (networkDef _ cs _ _ _) = cs

getCompStmName : 𝐁.CompStm → 𝐁.VariableName
getCompStmName (isomorphicTo x) = x
getCompStmName (equalTo x) = x

getInputDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.InputDefinition
getInputDefsᵇ (networkDef _ _ is _ _) = is

getOutputDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.OutputDefinition
getOutputDefsᵇ (networkDef _ _ _ _ os) = os

getNetworkNameᵇ : 𝐁.NetworkDefinition → 𝐁.VariableName
getNetworkNameᵇ (networkDef x _ _ _ _) = x

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

inclNetworkDefsCompStm : 𝐁.NetworkDefinition → Bool
inclNetworkDefsCompStm (networkDef _ cs _ _ _) = 1 ≤ᵇ List.length cs

inclNetworkDefsHiddenDefs : 𝐁.NetworkDefinition → Bool
inclNetworkDefsHiddenDefs (networkDef _ _ _ hs _) = 1 ≤ᵇ List.length hs
