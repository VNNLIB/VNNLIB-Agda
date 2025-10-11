module syntax-utils where

open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import Data.String as String hiding (toList)
open import Data.Nat as ℕ
open import Data.Bool
open import Data.Integer as ℤ using (ℤ; _◃_)
open import Data.Sign
open import Data.Maybe using (Maybe;nothing;just)
open import Data.Rational using (ℚ ; -_; ↧ₙ_; ↥_)
open import Agda.Builtin.Float
open import Data.Nat.Show as ℕshow using (show)

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

-- This returns a List would should return a Maybe instead
getCompStms : 𝐁.NetworkDefinition → List 𝐁.CompStm
getCompStms (networkDef x c is hs os) = c

getCompStmName : 𝐁.CompStm → 𝐁.VariableName
getCompStmName (isomorphicTo x) = x
getCompStmName (equalTo x) = x

getInputDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.InputDefinition
getInputDefsᵇ (networkDef x cs is hs os) = is

getOutputDefsᵇ : 𝐁.NetworkDefinition → List 𝐁.OutputDefinition
getOutputDefsᵇ (networkDef x cs is hs os) = os

getNetworkNameᵇ : 𝐁.NetworkDefinition → 𝐁.VariableName
getNetworkNameᵇ (networkDef x is cs hs os) = x

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
getHiddenDefsᵇ (networkDef x cs is hs os) = hs

inclNetworkDefsHiddenDefs : 𝐁.NetworkDefinition → Bool
inclNetworkDefsHiddenDefs n = let hs = (getHiddenDefsᵇ n) in 1 ≤ᵇ List.length hs

--- Parsing various numerical constants ---
open import Data.String as String using (String; _++_)
open import Data.List using (List; takeWhile; dropWhile; _++_; foldl)
open import Data.Char as Char using (Char; isDigit)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; case_of_)
open import Data.Product
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Data.List.Relation.Unary.Any as RUAny
open import Relation.Nullary
open import Data.Nat.Show
open import Data.Rational using (normalize)

isDigitChars : List Char → Bool
isDigitChars chars = List.foldl (λ z z₁ → isDigit z₁ ∧ z) true chars

getNumberString : List Char → Maybe String
getNumberString [] = just "0"
getNumberString (x ∷ chars) = let allChars = (x ∷ chars) in if isDigitChars allChars then just (String.fromList allChars) else nothing 

-- check if the char list has some prefix, and return a pair with it stripped
prefixedChars : Char → List Char → List Char × Bool
prefixedChars pfx [] = [] , false
prefixedChars pfx (x ∷ chars) = if x Char.== pfx then chars , true else x ∷ chars , false

getDouble : List Char → List Char → Maybe (String × String × Bool)
getDouble int dec with prefixedChars '-' int | prefixedChars '.' dec
... | int' , sign | dec' , _ with getNumberString int' | getNumberString dec'
... | just x | just x₁ = just (x , x₁ , sign)
... | just x | nothing = nothing
... | nothing | just x = nothing
... | nothing | nothing = nothing

parseDouble : String → Maybe (String × String × Bool)
parseDouble str = let chars = breakᵇ (λ z →  z Char.== '.') (String.toList str) in getDouble (proj₁ chars) (proj₂ chars)

readMaybeℕ×ℕ×Sign : String → Maybe (ℕ × ℕ × Bool)
readMaybeℕ×ℕ×Sign strNum with parseDouble strNum
... | nothing = nothing
... | just (nat₁ , nat₂ , sign) with readMaybe 10 nat₁ | readMaybe 10 nat₂
... | just _ | nothing = nothing
... | nothing | just _ = nothing
... | nothing | nothing = nothing
... | just nat₁' | just nat₂' = just (nat₁' , nat₂' , sign )

ℕ×ℕ×SignToℚ : (ℕ × ℕ × Bool) → ℚ
ℕ×ℕ×SignToℚ (int , frac , sign) with frac ℕ.≟ 0
... | yes _ = let rat = normalize int 1 in if sign then -_ rat else rat
... | no ¬p with 10 ^ List.length (String.toList (ℕshow.show frac)) ℕ.≟ 0 -- TODO: find better proof
... | yes _ = let rat = normalize int 1 in if sign then -_ rat else rat -- -- as this will always be unreachable
... | no ¬p =
    let
      denom = 10 ^ List.length (String.toList (ℕshow.show frac))
      numer = (int ℕ.* denom) ℕ.+ frac
      rat = normalize numer denom ⦃ ≢-nonZero ¬p ⦄
    in if sign then -_ rat else rat

parseReal : 𝐁.Number → Maybe ℚ
parseReal num with readMaybeℕ×ℕ×Sign ⟦ num ⟧asStringₙ
... | nothing = nothing
... | just nxnxs = just (ℕ×ℕ×SignToℚ nxnxs)

parseFloat64 : 𝐁.Number → Maybe Float
parseFloat64 num with parseReal num
... | nothing = nothing
... | just rat = just (primFloatDiv (primIntToFloat (↥_ rat)) (primNatToFloat (↧ₙ_ rat)))

-- Placeholder for unimplemented
postulate parseNumberPlaceholder : (τ : 𝐄.ElementType) → 𝐁.Number → Maybe (ElementTypeToSet τ)

parseNumber : (τ : 𝐄.ElementType) → 𝐁.Number → Maybe (ElementTypeToSet τ)
parseNumber real num = parseReal num
parseNumber τ num = parseNumberPlaceholder τ num

