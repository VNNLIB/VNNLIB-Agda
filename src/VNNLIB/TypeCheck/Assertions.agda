open import VNNLIB.Syntax as 𝐕
open import Data.List as List
open import VNNLIB.TypeCheck.Declarations

module VNNLIB.TypeCheck.Assertions (Σ : List 𝐕.NetworkDefinition) where

open import Data.Nat as ℕ
open import Data.Product as Product using (proj₁; proj₂; _,_; _×_)
open import Data.Bool as Bool
open import Data.Integer as ℤ using (∣_∣)
open import Data.String as String using (String; _==_)
open import Data.String.Properties
open import Data.Fin as Fin
open import Data.List.NonEmpty as List⁺
open import Data.List.Relation.Unary.Any as RUAny
open import Data.List.Properties using (length-map)
open import Data.List.NonEmpty as List⁺
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; subst; module ≡-Reasoning; cong₂)
open Eq.≡-Reasoning
open import Relation.Nullary
open import Relation.Unary
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Show
open import Function
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤;tt)
open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import VNNLIB.Syntax.AST as 𝐁 hiding (String)
open import VNNLIB.Types as 𝐄
open import VNNLIB.SyntaxUtils
open import Data.RationalUtils
open import Data.FloatUtils
open import Data.Tensor as 𝐓
open import VNNLIB.TypeCheck.ContextLemmas

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad
open RawMonad monad
open NetworkType

Γ : Context
Γ = mkContext Σ

validIndices : List 𝐁.Number → (s : 𝐓.TensorShape) → Result (𝐓.TensorIndices s)
validIndices [] [] = success 𝐓.empty
validIndices [] (x ∷ s) = error "Not enough indices for tensor shape"
validIndices (x ∷ xs) [] with x | xs -- for tensors declared with no shape i.e. scalars
... | number x₁ | [] = do
  x₁' ← convertMaybeToResult (readMaybe 10 ⟦ number x₁ ⟧asStringₙ)
  if x₁' ≡ᵇ ℕ.zero then success 𝐓.empty else error "Too many indices for tensor shape"
... | number x₁ | x₂ ∷ b = error "Too many indices for tensor shape"
validIndices (x ∷ xs) (n ∷ s) = do
  n' ← convertMaybeToResult (readMaybe 10 ⟦ x ⟧asStringₙ)
  idx ← convertMaybeToResult (toFin n n')
  rest ← validIndices xs s
  return (non-empty idx rest)

-- Converting an Input Index into an InputRef if refered for the expected element type
getInputRef :
  {n : NetworkRef Γ} →
  (j : Fin (List.length (inputShapes&Types (List.lookup Γ n)))) →
  (τ : 𝐄.ElementType) →
  Result (InputRef Γ n τ (proj₁ (List.lookup (NetworkType.inputShapes&Types (List.lookup Γ n)) j)))
getInputRef {n} j τ with τ ≡ᴱᵀ (proj₂ (List.lookup (NetworkType.inputShapes&Types (List.lookup Γ n)) j))
... | success p = success (inputRef)
  where
    shape = proj₁ (List.lookup (NetworkType.inputShapes&Types (List.lookup Γ n)) j)
    eqProof : (shape , τ) ≡ List.lookup (inputShapes&Types (List.lookup Γ n)) j
    eqProof = cong₂ _,_ refl p 
    inputRef : Any (_≡_ (shape , τ)) ((NetworkType.inputShapes&Types (List.lookup Γ n)))
    inputRef = indexToAny j eqProof
... | error _ = error "Input Type does not match assertion context"

-- Converting an Output Index into an OutputRef if refered for the expected element type
getOutputRef :
  {n : NetworkRef Γ} →
  (j : Fin (List.length (outputShapes&Types (List.lookup Γ n)))) →
  (τ : 𝐄.ElementType) →
  Result (OutputRef Γ n τ (proj₁ (List.lookup (NetworkType.outputShapes&Types (List.lookup Γ n)) j)))
getOutputRef {n} j τ with τ ≡ᴱᵀ (proj₂ (List.lookup (NetworkType.outputShapes&Types (List.lookup Γ n)) j))
... | success p = success (inputRef)
  where
    shape = proj₁ (List.lookup (NetworkType.outputShapes&Types (List.lookup Γ n)) j)
    eqProof : (shape , τ) ≡ List.lookup (outputShapes&Types (List.lookup Γ n)) j
    eqProof = cong₂ _,_ refl p 
    inputRef : Any (_≡_ (shape , τ)) ((NetworkType.outputShapes&Types (List.lookup Γ n)))
    inputRef = indexToAny j eqProof
... | error _ = error "Output Type does not match assertion context"


mutual
    inferArithExprType : 𝐁.ArithExpr → Maybe 𝐄.ElementType
    inferArithExprType (varExpr x xs) with getNetworkIndex Σ (convertVariableName x)
    ... | error _ = nothing
    ... | success n with getInputIndex (convertVariableName x) inputDefs | getOutputIndex (convertVariableName x) outputDefs
      where
       inputDefs = getInputDefs (List.lookup Σ n)
       outputDefs = getOutputDefs (List.lookup Σ n)
    ... | error x₁ | error x₂ = nothing -- out-of-scope (should be unreachable with checked declarations)
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
    ... | success n with getInputIndex (convertVariableName x) (getInputDefs (List.lookup Σ n)) | getOutputIndex (convertVariableName x) (getOutputDefs (List.lookup Σ n))
    ... | error x₁ | error x₂ = error x₁
    ... | error x₁ | success o = do
        let netRef = cast (length-Context Σ) n
        let outputInd = cast (length-outputs Σ n) o
        outputRef ← getOutputRef outputInd τ
        indices ← validIndices xs (proj₁ (List.lookup (outputShapes&Types (List.lookup Γ netRef)) outputInd))
        return (varOutput netRef outputRef indices)
    ... | success i | _ = do
        let netRef = cast (length-Context Σ) n
        let inputInd = cast (length-inputs Σ n) i
        inputRef ← getInputRef inputInd τ
        indices ← validIndices xs (proj₁ (List.lookup (inputShapes&Types (List.lookup Γ netRef)) inputInd))
        return (varInput netRef inputRef indices)
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
