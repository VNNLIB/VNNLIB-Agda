open import ONNX.Syntax
open import ONNX.Parser

module VNNLIB.TypeCheck
  (theorySyntax : NetworkTheorySyntax)
  (theoryParser : NetworkTheoryParser theorySyntax)
  where

open import Data.List as List
open import Data.List.Properties using (length-map)
open import Data.List.NonEmpty as List⁺
open import Data.Bool as Bool
open import Data.String as String using (String; _==_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Data.Fin as Fin
open import Data.Nat as ℕ
open import Data.List.Relation.Unary.Any as RUAny
open import Relation.Nullary
open import Data.Nat.Show
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base as Product
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.Unit
open import Level
open import Effect.Monad
open import Function.Base using (_$_; case_of_; flip)
import Relation.Nullary.Decidable as Dec
open import Data.List.Relation.Unary.Unique.DecPropositional using (unique?)

open import Data.Tensor as 𝐓
open import Data.RationalUtils
open import Data.FloatUtils
import Data.List.NonEmpty.Relation.Unary.Any as Any⁺
open import Data.ReadUtils

import VNNLIB.Syntax.AST as B hiding (String)
open import VNNLIB.Syntax theorySyntax
open import VNNLIB.TypeCheck.Monad

open NetworkTheorySyntax theorySyntax
private module Theory = NetworkTheoryParser theoryParser

---------------
-- Utilities --
---------------

unsupported : {A : Set} → String → TCM A
unsupported feature = throw ("Parser does not currently support" String.++ feature)

getVariableName : B.VariableName → String
getVariableName (B.variableName (B.#pair pos name)) = name

numberRep : B.Number → String
numberRep (B.number (B.#pair pos name)) = name

showElementType : B.ElementType → String
showElementType B.genericElementType    = "Real"
showElementType B.elementTypeF16        = "float16"
showElementType B.elementTypeF32        = "float32"
showElementType B.elementTypeF64        = "float64"
showElementType B.elementTypeBF16       = "bfloat16"
showElementType B.elementTypeF8E4M3FN   = "float8e4m3fn"
showElementType B.elementTypeF8E5M2     = "float8e5m2"
showElementType B.elementTypeF8E4M3FNUZ = "float8e4m3fnuz"
showElementType B.elementTypeF8E5M2FNUZ = "float8e5m2fnuz"
showElementType B.elementTypeF4E2M1     = "float4e2m1"
showElementType B.elementTypeI8         = "int8"
showElementType B.elementTypeI16        = "int16"
showElementType B.elementTypeI32        = "int32"
showElementType B.elementTypeI64        = "int64"
showElementType B.elementTypeU8         = "uint8"
showElementType B.elementTypeU16        = "uint16"
showElementType B.elementTypeU32        = "uint32"
showElementType B.elementTypeU64        = "uint64"
showElementType B.elementTypeC64        = "complex64"
showElementType B.elementTypeC128       = "complex128"
showElementType B.elementTypeBool       = "bool"
showElementType B.elementTypeString     = "string"

-------------
-- Context --
-------------

liftNetwork : ∀ {Γ} (n : NetworkDeclaration Γ) → NetworkDeclaration Γ → NetworkDeclaration (Γ ∷ n)
liftNetwork _ (declareNetwork name inputs outputs) = declareNetwork name inputs outputs

TensorVarResult : NetworkContext → Set
TensorVarResult Γ = Σ (TensorType TheoryType) (λ τ → InputVariable Γ τ ⊎ OutputVariable Γ τ)

module _
  {A : Set}
  (getName : A → Name)
  (getType : A → TensorType TheoryType)
  where

  lookupNameInNodes :
    (xs : List A)
    (name : B.VariableName) →
    Maybe (Σ (TensorType TheoryType) (λ τ → Any (λ a → getType a ≡ τ) xs))
  lookupNameInNodes [] name = nothing
  lookupNameInNodes (x ∷ xs) name =
    if getName x String.== getVariableName name
      then just (getType x , here refl)
      else Maybe.map (Product.map₂ there) (lookupNameInNodes xs name)

  lookupNameInNonEmptyNodes :
    ∀ (Γ : NetworkContext) → 
    (xs : List⁺ A)
    (name : B.VariableName) →
    Maybe (Σ (TensorType TheoryType) (λ τ → (λ n → Any⁺.Any (λ a → getType a ≡ τ) xs) Γ))
  lookupNameInNonEmptyNodes Γ (x ∷ xs) name =
    if getName x String.== getVariableName name
      then just (getType x , Any⁺.here refl)
      else Maybe.map (Product.map₂ Any⁺.there) (lookupNameInNodes xs name)

lookupNameInInputs :
  ∀ {Γ} (n : NetworkDeclaration Γ) →
  B.VariableName →
  Maybe (Σ (TensorType TheoryType) (λ τ → AnyNetwork (λ m → Any⁺.Any (λ a → inputType a ≡ τ) (networkInputs m)) (Γ ∷ n)))
lookupNameInInputs {Γ} n name = Maybe.map (Product.map₂ here) (lookupNameInNonEmptyNodes inputName inputType (Γ ∷ n) (networkInputs n) name)
  
lookupNameInOutputs :
  ∀ {Γ} (n : NetworkDeclaration Γ) →
  B.VariableName →
  Maybe (Σ (TensorType TheoryType) (λ τ → AnyNetwork (λ n → Any⁺.Any (λ a → outputType a ≡ τ) (networkOutputs n)) (Γ ∷ n)))
lookupNameInOutputs {Γ} n name = Maybe.map (Product.map₂ here) (lookupNameInNonEmptyNodes outputName outputType (Γ ∷ n) (networkOutputs n) name)

lookupTensorVariableInNetwork : ∀ {Γ} (n : NetworkDeclaration Γ) → B.VariableName → Maybe (TensorVarResult (Γ ∷ n))
lookupTensorVariableInNetwork n name with lookupNameInInputs n name | lookupNameInOutputs n name
... | just (τ , i) | _            = just (τ , inj₁ i)
... | _            | just (τ , o) = just (τ , inj₂ o)
... | nothing      | nothing      = nothing

lookupTensorVariable : (Γ : NetworkContext) → B.VariableName → TCM (TensorVarResult Γ)
lookupTensorVariable []       name = throw "Missing tensor variable"
lookupTensorVariable (Γ ∷ n) name = do
  case lookupTensorVariableInNetwork n name of λ where
    (just result) → return result
    nothing → Product.map₂ (Sum.map there there) <$> lookupTensorVariable Γ name

variablesDeclared : ∀ {Γ} → NetworkDeclaration Γ → List Name
variablesDeclared n = do
  let inputNames = List.map inputName (List⁺.toList $ networkInputs n)
  let outputNames = List.map outputName (List⁺.toList $ networkOutputs n)
  networkName n ∷ List.concat (inputNames ∷ outputNames ∷ [])

allVariablesDeclared : NetworkContext → List Name
allVariablesDeclared [] = []
allVariablesDeclared (Γ ∷ x) = variablesDeclared x List.++ allVariablesDeclared Γ

-----------------
-- Declarations --
-----------------

-- TODO we should make this more efficient, caching a set rather than recomputing all names
checkNameUnique : (Γ : NetworkContext) → B.VariableName → TCM Name
checkNameUnique Γ name = do
  let name' = getVariableName name
  let names = allVariablesDeclared Γ
  case any? (String._≟ name') names of λ where
    (yes _) → throw "duplicate variables"
    (no _) → return name'

-- TODO we should make this more efficient, caching a set rather than recomputing all names
checkNamesLocallyUnique : ∀ {Γ} → NetworkDeclaration Γ → TCM ⊤
checkNamesLocallyUnique n = do
  let names = variablesDeclared n
  case unique? String._≟_ names of λ where
    (yes _) → return _
    (no _) → throw "duplicate variables"

checkShape : List B.Number → TCM TensorShape
checkShape [] = return []
checkShape (d ∷ ds) with readℕ₁₀ (numberRep d)
... | nothing = throw "unable to read number"
... | just d' = do
  ds' ← checkShape ds
  return (d' ∷ ds')

checkTensorShape : B.TensorShape → TCM (List ℕ)
checkTensorShape B.scalarDims = return []
checkTensorShape (B.tensorDims xs) = checkShape xs

checkTheoryType : B.ElementType → TCM TheoryType
checkTheoryType τ with Theory.readType (showElementType τ)
... | just r  = return r
... | nothing = throw "Could not parse type"

checkEquivalenceStatements : List B.CompStm → TCM ⊤
checkEquivalenceStatements [] = return _
checkEquivalenceStatements (_ ∷ _) = unsupported "equivalence statements"

checkInputDeclaration : NetworkContext → B.InputDefinition → TCM (InputDeclaration)
checkInputDeclaration Γ (B.inputDef varName τ shape) = do
  name' ← checkNameUnique Γ varName
  shape' ← checkTensorShape shape
  τ' ← checkTheoryType τ
  return (declareInput name' (tensorType τ' shape'))
checkInputDeclaration _ _ = unsupported "named outputs"

checkInputDeclarations : NetworkContext → List B.InputDefinition → TCM (List⁺ InputDeclaration)
checkInputDeclarations Γ [] = throw "Must be at least one input definition"
checkInputDeclarations Γ (x ∷ xs) = do
  x' ← checkInputDeclaration Γ x
  xs' ← traverseTCMList (checkInputDeclaration Γ) xs
  return (x' ∷ xs')

checkHiddenDeclarations : List B.HiddenDefinition → TCM ⊤
checkHiddenDeclarations [] = return _
checkHiddenDeclarations (_ ∷ _) = throw "Parser does not currently support hidden definitions"

checkOutputDeclaration : NetworkContext → B.OutputDefinition → TCM OutputDeclaration
checkOutputDeclaration Γ (B.outputDef varName e t) = do
  name ← checkNameUnique Γ varName
  t' ← checkTensorShape t
  e' ← checkTheoryType e
  return (declareOutput name (tensorType e' t'))
checkOutputDeclaration _ _ = unsupported "named outputs"

checkOutputDeclarations : NetworkContext → List B.OutputDefinition → TCM (List⁺ OutputDeclaration)
checkOutputDeclarations Γ [] = throw "Must be at least one output definition"
checkOutputDeclarations Γ (x ∷ xs) = do
  x' ← checkOutputDeclaration Γ x
  xs' ← traverseTCMList (checkOutputDeclaration Γ) xs
  return (x' ∷ xs')

checkNetworkDeclaration : ∀ Γ → B.NetworkDefinition → TCM (NetworkDeclaration Γ)
checkNetworkDeclaration Γ (B.networkDef varName equivs inputs hidden outputs) = do
  name ← checkNameUnique Γ varName
  checkEquivalenceStatements equivs
  inputs ← checkInputDeclarations Γ inputs
  checkHiddenDeclarations hidden
  outputs ← checkOutputDeclarations Γ outputs
  let decl = declareNetwork name inputs outputs
  checkNamesLocallyUnique decl
  return decl

checkNetworks : List B.NetworkDefinition → TCM NetworkContext
checkNetworks [] = return []
checkNetworks (n ∷ ns) = do
  ns' ← checkNetworks ns
  n' ← checkNetworkDeclaration ns' n
  return (ns' ∷ n')

----------------
-- Assertions --
----------------

checkIndices : List B.Number → (s : 𝐓.TensorShape) → TCM (𝐓.TensorIndices s)
checkIndices []        []       = return []
checkIndices []        (_ ∷ _) = throw "Not enough indices for tensor shape"
checkIndices (_ ∷ _)  []       = throw "Too many indices for tensor shape"
checkIndices (i ∷ is) (d ∷ ds) = do
  i' ← convertMaybeToResult (readMaybe 10 (numberRep i))
  idx ← convertMaybeToResult (toFin d i')
  rest ← checkIndices is ds
  return (idx ∷ rest)

module _ (Γ : NetworkContext) where

  checkNumber : B.Number → (τ : TheoryType) → TCM (ArithExpr Γ τ)
  checkNumber num τ with Theory.readNumber τ (numberRep num)
  ... | just value = return $ constant value
  ... | nothing = throw "Cannot parse onnx number"

  checkVariable : B.VariableName → List B.Number → TCM (Σ TheoryType (ArithExpr Γ))
  checkVariable varName indices = do
    (tensorType τ shape , var) ← lookupTensorVariable Γ varName
    indices' ← checkIndices indices shape
    let expr = case var of λ where
      (inj₁ input) → inputVar (elementVar shape input indices')
      (inj₂ output) → outputVar (elementVar shape output indices')
    return (τ , expr)
    
  mutual
    inferArithExpr : B.ArithExpr → Inference (ArithExpr Γ)
    inferArithExpr (B.valExpr x)           = unknownType $ checkNumber x
    inferArithExpr (B.varExpr var indices) = knownType $ checkVariable var indices
    inferArithExpr (B.negate a)            = mapInference negate (inferArithExpr a)
    inferArithExpr (B.plus as)             = mapInference add (inferList⁺ArithExpr as)
    inferArithExpr (B.minus a as)          = mapInference sub (inferList⁺ArithExpr (a ∷ as))
    inferArithExpr (B.multiply as)         = mapInference mul (inferList⁺ArithExpr as)

    inferList⁺ArithExpr : List B.ArithExpr → Inference (λ τ → List⁺ (ArithExpr Γ τ))
    inferList⁺ArithExpr [] = knownType $ throw "Boolean operators must have at least one argument"
    inferList⁺ArithExpr (x ∷ xs) = zipInference Theory._≟_ _∷_ (inferArithExpr x) (inferListArithExpr xs)
    
    inferListArithExpr : List B.ArithExpr → Inference (λ τ → List (ArithExpr Γ τ))
    inferListArithExpr []        = unknownType $ λ τ → return [] 
    inferListArithExpr (x ∷ xs) = zipInference Theory._≟_ _∷_ (inferArithExpr x) (inferListArithExpr xs)

  checkComparison :
    ({τ : TheoryType} → ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ) →
    B.ArithExpr →
    B.ArithExpr →
    TCM (Σ TheoryType (CompExpr Γ))
  checkComparison f e₁ e₂ = do
    let inference = zipInference Theory._≟_ f (inferArithExpr e₁) (inferArithExpr e₂)
    case inference of λ where
      (unknownType _) → throw "unable to infer the type of the arithmetic expression"
      (knownType action) → action

  mutual
    checkBoolExpr : B.BoolExpr → TCM (BoolExpr Γ)
    checkBoolExpr (B.greaterThan  e₁ e₂) = compExpr <$> checkComparison greaterThan  e₁ e₂
    checkBoolExpr (B.lessThan     e₁ e₂) = compExpr <$> checkComparison lessThan     e₁ e₂
    checkBoolExpr (B.greaterEqual e₁ e₂) = compExpr <$> checkComparison greaterEqual e₁ e₂
    checkBoolExpr (B.lessEqual    e₁ e₂) = compExpr <$> checkComparison lessEqual    e₁ e₂
    checkBoolExpr (B.notEqual     e₁ e₂) = compExpr <$> checkComparison notEqual     e₁ e₂
    checkBoolExpr (B.equal        e₁ e₂) = compExpr <$> checkComparison equal        e₁ e₂
    checkBoolExpr (B.and es)    = andExpr  <$> checkList⁺BoolExpr es
    checkBoolExpr (B.or  es)    = orExpr   <$> checkList⁺BoolExpr  es
    
    checkList⁺BoolExpr : List B.BoolExpr → TCM (List⁺ (BoolExpr Γ))
    checkList⁺BoolExpr [] = throw "Boolean operators must have at least one argument"
    checkList⁺BoolExpr (x ∷ xs) = do
      x' ← checkBoolExpr x
      xs' ← checkListBoolExpr xs
      return $ x' ∷ xs'
    
    checkListBoolExpr : List B.BoolExpr → TCM (List (BoolExpr Γ))
    checkListBoolExpr [] = return []
    checkListBoolExpr (x ∷ xs) = do
        x' ← checkBoolExpr x
        xs' ← checkListBoolExpr xs
        return (x' ∷ xs')
    
  checkAssertion : B.Assertion → TCM (Assertion Γ)
  checkAssertion (B.assert expr) = assert <$> checkBoolExpr expr
  
  checkAssertions : List B.Assertion → TCM (List (Assertion Γ))
  checkAssertions = traverseTCMList checkAssertion

-----------
-- Query --
-----------

checkQuery : B.Query → TCM Query
checkQuery (B.vNNLibQuery ver networks assertions) = do
  networks' ← checkNetworks networks
  assertions' ← checkAssertions networks' assertions
  return (query networks' assertions')
