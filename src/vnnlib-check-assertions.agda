{-# OPTIONS --allow-unsolved-metas #-}
open import vnnlib-syntax as 𝐕
open import Data.List as List
open import vnnlib-check-declarations
module vnnlib-check-assertions (Σ : List 𝐕.NetworkDefinition) where

open import Data.Nat as ℕ
open import Data.Product as Product using (proj₁; proj₂; _,_)
open import Data.Bool as Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.String as String using (String; _==_)
open import Data.String.Properties
open import Data.Fin as Fin
open import Data.List.NonEmpty as List⁺
open import Data.List.Relation.Unary.Any as RUAny
open import Data.List.Properties using (length-map)
open import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; subst; module ≡-Reasoning)
open Eq.≡-Reasoning
open import Relation.Nullary
open import Data.Maybe hiding (_>>=_)
open import Function

open import Syntax.AST as 𝐁 hiding (String)
open import vnnlib-types as 𝐄
open import syntax-utils
open import types-utils
open import tensor as 𝐓
open import context-isomorphism

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad
open RawMonad monad
open NetworkType

Γ : Context
Γ = mkContext Σ

postulate validIndices : List 𝐁.Number → (s : 𝐓.TensorShape) → Result (𝐓.TensorIndices s)

mutual
    inferArithExprType : 𝐁.ArithExpr → Maybe 𝐄.ElementType
    inferArithExprType (varExpr x xs) with getNetworkIndex Σ (convertVariableName x)
    ... | error _ = nothing
    ... | success n with getInputIndex (convertVariableName x) inputDefs | getOutputIndex (convertVariableName x) outputDefs
      where
       inputDefs = getInputDefs (List.lookup Σ n)
       outputDefs = getOutputDefs (List.lookup Σ n)
    ... | error x₁ | error x₂ = nothing -- out-of-scope (should be unreachable)
    ... | error x₁ | success y = just (getElementTypeₒ (List.lookup (getOutputDefs (List.lookup Σ n)) y))
    ... | success y | _ = just (getElementTypeᵢ (List.lookup (getInputDefs (List.lookup Σ n)) y))
    inferArithExprType (valExpr x) = nothing
    inferArithExprType (negate a) = inferArithExprType a
    inferArithExprType (plus as) = inferListArithExprType as
    inferArithExprType (minus a as) = inferListArithExprType (a ∷ as)
    inferArithExprType (multiply as) = inferListArithExprType as

    inferListArithExprType : List 𝐁.ArithExpr → Maybe 𝐄.ElementType
    inferListArithExprType [] = nothing
    inferListArithExprType (x ∷ xs) with inferArithExprType x | inferListArithExprType xs
    ... | just x₁ | just x₂ = just x₁
    ... | just x₁ | nothing = just x₁
    ... | nothing | just x₁ = just x₁
    ... | nothing | nothing = nothing

mutual
    checkArithExpr : (τ : 𝐄.ElementType) → 𝐁.ArithExpr → Result (𝐕.ArithExpr Γ τ)
    checkArithExpr τ (valExpr x) with parseNumber τ x
    ... | just t = success (constant t)
    ... | nothing = error "Cannot parse number"
    checkArithExpr τ (varExpr x xs) with getNetworkIndex Σ (convertVariableName x)
    ... | error e = error e
    ... | success n with getInputIndex (convertVariableName x) (getInputDefs (List.lookup Σ n))
    ...   | success i = if isSameType τ (getElementTypeᵢ inputDecl) then success (varInput networkInd inputInd {!!}) else error "Variable type mismatch"
        where
          inputDecl : 𝐕.InputDefinition
          inputDecl = List.lookup (getInputDefs (List.lookup Σ n)) i
        
          networkInd : Fin (List.length Γ)
          networkInd = cast (length-Context Σ) n

          inputInd : Fin (List.length (inputShapes&Types (List.lookup (mkContext Σ) (cast (length-Context Σ) n))))
          inputInd = cast (length-inputs Σ n) i

          tensorShape = proj₁ (List.lookup (inputShapes&Types (List.lookup Γ networkInd)) inputInd)
          indices = validIndices xs tensorShape
    ... | error _ with getOutputIndex (convertVariableName x) (getOutputDefs (List.lookup Σ n))
    ... | error _ = error ""
    ... | success o = if isSameType τ (getElementTypeₒ outputDecl) then success (varOutput networkInd outputInd {!!}) else error "Variable type mismatch"
        where
          outputDecl : 𝐕.OutputDefinition
          outputDecl = List.lookup (getOutputDefs (List.lookup Σ n)) o
        
          networkInd : Fin (List.length Γ)
          networkInd = cast (length-Context Σ) n

          outputInd : Fin (List.length (outputShapes&Types (List.lookup (mkContext Σ) (cast (length-Context Σ) n))))
          outputInd = cast (length-outputs Σ n) o

          tensorShape = proj₁ (List.lookup (outputShapes&Types (List.lookup Γ networkInd)) outputInd)
          indices = validIndices xs tensorShape
    checkArithExpr τ (negate a) with checkArithExpr τ a
    ... | error e = error e
    ... | success x = success (negate x)
    checkArithExpr τ (plus as) = do
        as' ← checkListArithExpr τ as
        return (add as')
    checkArithExpr τ (minus a as) = do
        as' ← checkListArithExpr τ as
        a' ← checkArithExpr τ a
        return (minus (a' ∷ as'))
    checkArithExpr τ (multiply as) = do
        as' ← checkListArithExpr τ as
        return (mult as')

    checkListArithExpr : (τ : 𝐄.ElementType) → List 𝐁.ArithExpr → Result (List (𝐕.ArithExpr Γ τ))
    checkListArithExpr τ [] = success [] 
    checkListArithExpr τ (x ∷ xs) = do
        x' ← checkArithExpr τ x
        xs' ← checkListArithExpr τ xs
        return (x' ∷ xs')

-- check boolean expressions
checkCompExpr : ({τ : 𝐄.ElementType} → 𝐕.ArithExpr Γ τ → 𝐕.ArithExpr Γ τ → 𝐕.BoolExpr Γ) → 𝐁.ArithExpr → 𝐁.ArithExpr → Result(𝐕.BoolExpr Γ)
checkCompExpr f b₁ b₂ = do
    let type = findType b₁ b₂
    t₁ ← checkArithExpr type b₁
    t₂ ← checkArithExpr type b₂
    return (f t₁ t₂)
    where
        findType : 𝐁.ArithExpr → 𝐁.ArithExpr → 𝐄.ElementType
        findType b₁ b₂ with inferArithExprType b₁ |  inferArithExprType b₂
        ... | just x | just x₁ = x
        ... | just x | nothing = x
        ... | nothing | just x = x
        ... | nothing | nothing = real

-- wrapper function for checkCompExpr
checkComparative : ({τ : 𝐄.ElementType} → 𝐕.ArithExpr Γ τ → 𝐕.ArithExpr Γ τ → 𝐕.CompExpr Γ τ) → 𝐁.ArithExpr → 𝐁.ArithExpr → Result(𝐕.BoolExpr Γ)
checkComparative f b₁ b₂ = checkCompExpr (λ x x₁ → compExpr (_ , f x x₁)) b₁ b₂

mutual
    checkBoolExpr : 𝐁.BoolExpr → Result (𝐕.BoolExpr Γ)
    checkBoolExpr (greaterThan a₁ a₂) = checkComparative greaterThan a₁ a₂
    checkBoolExpr (lessThan a₁ a₂) = checkComparative lessThan a₁ a₂
    checkBoolExpr (greaterEqual a₁ a₂) = checkComparative greaterEqual a₁ a₂
    checkBoolExpr (lessEqual a₁ a₂) = checkComparative lessEqual a₁ a₂
    checkBoolExpr (notEqual a₁ a₂) = checkComparative notEqual a₁ a₂
    checkBoolExpr (equal a₁ a₂) = checkComparative equal a₁ a₂
    checkBoolExpr (BoolExpr.and bs) = do
        bs' ← checkListBoolExpr bs
        return (andExpr bs')
    checkBoolExpr (BoolExpr.or bs) = do
        bs' ← checkListBoolExpr bs
        return (orExpr bs')

    checkListBoolExpr :  List 𝐁.BoolExpr →  Result (List (𝐕.BoolExpr Γ))
    checkListBoolExpr [] = success []
    checkListBoolExpr (x ∷ xs) = do
        x' ← checkBoolExpr x
        xs' ← checkListBoolExpr xs
        return (x' ∷ xs')
