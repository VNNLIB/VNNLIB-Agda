open import ONNX.Syntax
open import ONNX.Parser

module VNNLIB.Parser
  (theorySyntax : NetworkTheorySyntax)
  (theoryParser : NetworkTheoryParser theorySyntax)
  where

open import Data.List as List using (List; []; _∷_)
open import Data.List.Properties using (length-map; ≡-dec)
open import Data.List.NonEmpty as List⁺ hiding (_∷⁺_)
import Data.List.NonEmpty.Properties as List⁺
open import Data.List.NonEmpty.Relation.Binary.Pointwise as NonEmpty
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
open import Function.Base using (_$_; _∘_; case_of_; flip)
import Relation.Nullary.Decidable as Dec
open import Data.List.Relation.Unary.Unique.DecPropositional using (unique?)

open import Data.Tensor as 𝐓
open import Data.RationalUtils
open import Data.FloatUtils
import Data.List.NonEmpty.Relation.Unary.Any as Any⁺
import Data.List.NonEmpty.Membership.Propositional as Any⁺
open import Data.ReadUtils

import VNNLIB.Grammar.AST as B
import VNNLIB.Grammar.Parser as B using (parseQuery; Err)
open import VNNLIB.Syntax theorySyntax
open import VNNLIB.Parser.Monad

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

-------------
-- Context --
-------------

TensorVarResult : NetworkDeclarations → Set
TensorVarResult Γ = Σ (TensorType ElementType) (λ τ → InputVariable Γ τ ⊎ HiddenVariable Γ τ ⊎ OutputVariable Γ τ)

module _
  {A : Set}
  (getType : A → TensorType ElementType)
  (getName : A → String)
  where

  lookupNameInNodes :
    (xs : List A)
    (name : B.VariableName) →
    Maybe (Σ (TensorType ElementType) (_∈ List.map getType xs))
  lookupNameInNodes [] name = nothing
  lookupNameInNodes (x ∷ xs) name =
    if getName x String.== getVariableName name
      then just (getType x , here refl)
      else Maybe.map (Product.map₂ there) (lookupNameInNodes xs name)

  lookupNameInNonEmptyNodes :
    (xs : List⁺ A)
    (name : B.VariableName) →
    Maybe (Σ (TensorType ElementType) (Any⁺._∈ List⁺.map getType xs))
  lookupNameInNonEmptyNodes (x ∷ xs) name =
    if getName x String.== getVariableName name
      then just (getType x , Any⁺.here refl)
      else Maybe.map (Product.map₂ Any⁺.there) (lookupNameInNodes xs name)
  
lookupNameInInputs :
  ∀ (n : NetworkDeclaration) →
  B.VariableName →
  Maybe (Σ (TensorType ElementType) (λ δ → HasInputDeclarationMatching δ n))
lookupNameInInputs n name = lookupNameInNonEmptyNodes inputType inputName (inputDeclarations n) name
  
lookupNameInHidden :
  ∀ (n : NetworkDeclaration) →
  B.VariableName →
  Maybe (Σ (TensorType ElementType) (λ δ → HasHiddenDeclarationMatching δ n))
lookupNameInHidden n name = lookupNameInNodes hiddenType hiddenName (hiddenDeclarations n) name
  
lookupNameInOutputs :
  ∀ (n : NetworkDeclaration) →
  B.VariableName →
  Maybe (Σ (TensorType ElementType) (λ δ → HasOutputDeclarationMatching δ n))
lookupNameInOutputs n name = lookupNameInNonEmptyNodes outputType outputName (outputDeclarations n) name

lookupTensorVariableInNetwork : ∀ {Γ} (n : NetworkDeclaration) → B.VariableName → Maybe (TensorVarResult (n ∷ Γ))
lookupTensorVariableInNetwork n name with lookupNameInInputs n name | lookupNameInHidden n name | lookupNameInOutputs n name
... | just (τ , i) | _            | _            = just (τ , inj₁ (here i))
... | _            | just (τ , h) | _            = just (τ , inj₂ (inj₁ (here h)))
... | _            | _            | just (τ , o) = just (τ , inj₂ (inj₂ (here o)))
... | nothing      | nothing      | nothing      = nothing

lookupTensorVariable : (Γ : NetworkDeclarations) → B.VariableName → TCM (TensorVarResult Γ)
lookupTensorVariable []       name = throw "Missing tensor variable"
lookupTensorVariable (n ∷ Γ) name = do
  case lookupTensorVariableInNetwork n name of λ where
    (just result) → return result
    nothing → Product.map₂ (Sum.map there (Sum.map there there)) <$> lookupTensorVariable Γ name

variablesDeclared : NetworkDeclaration → List Name
variablesDeclared n = do
  let inputNames = List.map inputName (List⁺.toList $ inputDeclarations n)
  let hiddenNames = List.map hiddenName (hiddenDeclarations n)
  let outputNames = List.map outputName (List⁺.toList $ outputDeclarations n)
  networkName n ∷ List.concat (inputNames ∷ hiddenNames ∷ outputNames ∷ [])

allVariablesDeclared : NetworkDeclarations → List Name
allVariablesDeclared [] = []
allVariablesDeclared (x ∷ Γ) = variablesDeclared x List.++ allVariablesDeclared Γ

isTensorTypeEqual : DecidableEquality (TensorType ElementType)
isTensorTypeEqual (tensorType tensorType₁ tensorDims₁) (tensorType tensorType₂ tensorDims₂)
  with tensorType₁ Theory.≟ tensorType₂ | tensorDims₁ shape-≟ tensorDims₂
... | yes p | yes t = yes (cong₂ tensorType p t)
... | no ¬p | _     = no λ {refl → ¬p refl} 
... | _     | no ¬t = no λ {refl → ¬t refl}

isTensorShapeEqual : Decidable (TensorShapesMatch {ElementType} {ElementType})
isTensorShapeEqual xs ys = TensorType.tensorDims xs shape-≟ TensorType.tensorDims ys

isNetworkTypeEqual : DecidableEquality (NetworkType ElementType)
isNetworkTypeEqual (networkType inputs₁ outputs₁) (networkType inputs₂ outputs₂)
  with NonEmpty.decidableEq isTensorTypeEqual inputs₁ inputs₂
     | NonEmpty.decidableEq isTensorTypeEqual outputs₁ outputs₂
... | yes eq₁ | yes eq₂ = yes (cong₂ networkType eq₁ eq₂)
... | no ¬eq₁ | _       = no λ {refl → ¬eq₁ refl}
... | _       | no ¬eq₂ = no λ {refl → ¬eq₂ refl}
  
isNetworkShapeEqual : (γ₁ : NetworkType ElementType) (γ₂ : NetworkType ElementType) → Maybe (NetworkShapesMatch γ₁ γ₂)
isNetworkShapeEqual (networkType inputs₁ outputs₁) (networkType inputs₂ outputs₂)
  with NonEmpty.decidable isTensorShapeEqual inputs₁ inputs₂
     | NonEmpty.decidable isTensorShapeEqual outputs₁ outputs₂
... | yes eq₁ | yes eq₂ = just (eq₁ , eq₂)
... | no ¬eq₁ | _       = nothing
... | _       | no ¬eq₂ = nothing

checkTargetNetworkEquivStatements : (d : NetworkDeclaration) → Maybe (equivalence d ≡ none)
checkTargetNetworkEquivStatements (declareNetwork _ _ _ _ equiv) with equiv
... | none = just refl
... | _    = nothing

lookupEqualNetwork :
  (Γ : NetworkDeclarations) →
  (name : Name) →
  (d : NetworkDeclaration) →
  Maybe (Any (ValidEqualToTarget name d) Γ)
lookupEqualNetwork [] _ _ = nothing
lookupEqualNetwork (d₂ ∷ Γ) name d₁
  with name String.≟ networkName d₂
     | checkTargetNetworkEquivStatements d₂
     | isNetworkTypeEqual (typeOfNetwork d₁) (typeOfNetwork d₂)
... | no _       | _       | _       = Maybe.map there (lookupEqualNetwork Γ name d₁)
... | yes nameEq | just e₁ | yes e₂ = just (here (validEqualTo e₁ e₂ nameEq))
... | yes _      | _       | _       = nothing

lookupIsomorphicNetwork :
  (Γ : NetworkDeclarations) →
  (name : Name) →
  (d : NetworkDeclaration) →
  Maybe (Any (ValidIsomorphicToTarget name d) Γ)
lookupIsomorphicNetwork [] _ _ = nothing
lookupIsomorphicNetwork (d₂ ∷ Γ) name d₁
  with name String.≟ networkName d₂
     | checkTargetNetworkEquivStatements d₂
     | isNetworkShapeEqual (typeOfNetwork d₁) (typeOfNetwork d₂)
... | no _       | _       | _       = Maybe.map there (lookupIsomorphicNetwork Γ name d₁)
... | yes nameEq | just e₁ | just e₂ = just (here (validIsomorphicTo e₁ e₂ nameEq))
... | yes _      | _       | _       = nothing

checkValidEquivalence : (Γ : NetworkDeclarations) (d : NetworkDeclaration) (e : NetworkEquivalence) → TCM (ValidNetworkEquivalence Γ d e)
checkValidEquivalence Γ d none = return none
checkValidEquivalence Γ d (equal-to x) with lookupEqualNetwork Γ x d
... | just e = return (equal-to e)
... | nothing = throw "Could not parse equal Equivalence statement"
checkValidEquivalence Γ d (isomorphic-to x) with lookupIsomorphicNetwork Γ x d
... | just e = return (isomorphic-to e)
... | nothing = throw "Could not parse isomorphic Equivalence statement"

checkValidEquivalences : (Γ : NetworkDeclarations) → TCM (ValidNetworkEquivalences Γ)
checkValidEquivalences [] = return []
checkValidEquivalences (d ∷ Γ) = do
  e ← checkValidEquivalence Γ d (equivalence d)
  es ← checkValidEquivalences Γ
  return (e ∷ es)

-----------------
-- Declarations --
-----------------

-- TODO we should make this more efficient, caching a set rather than recomputing all names
checkNameUnique : (Γ : NetworkDeclarations) → B.VariableName → TCM Name
checkNameUnique Γ name = do
  let name' = getVariableName name
  let names = allVariablesDeclared Γ
  case any? (String._≟ name') names of λ where
    (yes _) → throw "duplicate variables"
    (no _) → return name'

-- TODO we should make this more efficient, caching a set rather than recomputing all names
checkNamesLocallyUnique :  NetworkDeclaration → TCM ⊤
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

checkNodeName : B.OnnxName → TCM NodeOutputName
checkNodeName (B.nodeName (B.onnxString value)) with Theory.readNodeOutputName value
... | nothing = throw "unable to read ONNX name"
... | just name = return name

checkTensorShape : B.TensorShape → TCM (List ℕ)
checkTensorShape B.scalarDims = return []
checkTensorShape (B.tensorDims xs) = checkShape xs

checkElementType : B.ElementType → TCM ElementType
checkElementType (B.dType τ) with Theory.readElementType (getVariableName τ)
... | just r  = return r
... | nothing = throw "Could not parse type"

checkEquivalenceStatement : B.NetworkEquivalence → TCM NetworkEquivalence
checkEquivalenceStatement (B.isomorphicTo x) = return (isomorphic-to (getVariableName x))
checkEquivalenceStatement (B.equalTo x)      = return (equal-to (getVariableName x))

checkEquivalenceStatements : List B.NetworkEquivalence → TCM NetworkEquivalence
checkEquivalenceStatements [] = return none
checkEquivalenceStatements (x ∷ []) = checkEquivalenceStatement x
checkEquivalenceStatements (x ∷ x₁ ∷ equivs) = throw "Must at most have one equivalence statement"

checkInputDeclaration : NetworkDeclarations → B.InputDefinition → TCM (InputDeclaration)
checkInputDeclaration Γ (B.inputDef varName τ shape) = do
  name' ← checkNameUnique Γ varName
  shape' ← checkTensorShape shape
  τ' ← checkElementType τ
  return (declareInput name' (tensorType τ' shape'))

checkInputDeclarations : NetworkDeclarations → List B.InputDefinition → TCM (List⁺ InputDeclaration)
checkInputDeclarations Γ [] = throw "Must be at least one input definition"
checkInputDeclarations Γ (x ∷ xs) = do
  x' ← checkInputDeclaration Γ x
  xs' ← traverseTCMList (checkInputDeclaration Γ) xs
  return (x' ∷ xs')

checkHiddenDeclaration : NetworkDeclarations → B.HiddenDefinition → TCM (HiddenDeclaration)
checkHiddenDeclaration Γ (B.hiddenDef varName τ shape node) = do
  name' ← checkNameUnique Γ varName
  shape' ← checkTensorShape shape
  τ' ← checkElementType τ
  nodeName' ← checkNodeName node
  return (declareHidden name' (tensorType τ' shape') nodeName')

checkHiddenDeclarations : NetworkDeclarations → List B.HiddenDefinition → TCM (List HiddenDeclaration)
checkHiddenDeclarations Γ = traverseTCMList (checkHiddenDeclaration Γ)

checkOutputDeclaration : NetworkDeclarations → B.OutputDefinition → TCM OutputDeclaration
checkOutputDeclaration Γ (B.outputDef varName e t) = do
  name ← checkNameUnique Γ varName
  t' ← checkTensorShape t
  e' ← checkElementType e
  return (declareOutput name (tensorType e' t'))

checkOutputDeclarations : NetworkDeclarations → List B.OutputDefinition → TCM (List⁺ OutputDeclaration)
checkOutputDeclarations Γ [] = throw "Must be at least one output definition"
checkOutputDeclarations Γ (x ∷ xs) = do
  x' ← checkOutputDeclaration Γ x
  xs' ← traverseTCMList (checkOutputDeclaration Γ) xs
  return (x' ∷ xs')

checkNetworkDeclaration : ∀ Γ → B.NetworkDefinition → TCM (NetworkDeclaration)
checkNetworkDeclaration Γ (B.networkDef varName equivs inputs hidden outputs) = do
  name ← checkNameUnique Γ varName
  inputs ← checkInputDeclarations Γ inputs
  hidden ← checkHiddenDeclarations Γ hidden
  outputs ← checkOutputDeclarations Γ outputs
  equivalence ← checkEquivalenceStatements equivs
  let decl = declareNetwork name inputs hidden outputs equivalence
  checkNamesLocallyUnique decl
  return decl

checkNetworks : List B.NetworkDefinition → TCM NetworkDeclarations
checkNetworks [] = throw "Must be at least one Network Declaration"
checkNetworks (n ∷ ns) = do
  ns' ← checkNetworks ns
  n' ← checkNetworkDeclaration ns' n
  return (n' ∷ ns')

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

module _ (Γ : NetworkDeclarations) where

  checkNumber : B.Number → (τ : ElementType) → TCM (ArithExpr Γ τ)
  checkNumber num τ with Theory.readNumber τ (numberRep num)
  ... | just value = return $ constant value
  ... | nothing = throw "Cannot parse onnx number"

  checkVariable : B.VariableName → List B.Number → TCM (Σ ElementType (ArithExpr Γ))
  checkVariable varName indices = do
    (tensorType τ shape , var) ← lookupTensorVariable Γ varName
    indices' ← checkIndices indices shape
    let expr = case var of λ where
      (inj₁ input) → inputVar (elementVar input indices')
      (inj₂ (inj₁ hidden)) → hiddenVar (elementVar hidden indices')
      (inj₂ (inj₂ output)) → outputVar (elementVar output indices')
    return (τ , expr)
    
  mutual
    inferArithExpr : B.ArithExpr → Inference (ArithExpr Γ)
    inferArithExpr (B.valExpr x)                 = unknownType $ checkNumber x
    inferArithExpr (B.scalarVarExpr var)         = knownType $ checkVariable var []
    inferArithExpr (B.tensorVarExpr var indices) = knownType $ checkVariable var indices
    inferArithExpr (B.negate a)                  = mapInference negate (inferArithExpr a)
    inferArithExpr (B.plus as)                   = mapInference add (inferList⁺ArithExpr as)
    inferArithExpr (B.minus a as)                = mapInference sub (inferList⁺ArithExpr (a ∷ as))
    inferArithExpr (B.multiply as)               = mapInference mul (inferList⁺ArithExpr as)

    inferList⁺ArithExpr : List B.ArithExpr → Inference (λ τ → List⁺ (ArithExpr Γ τ))
    inferList⁺ArithExpr [] = knownType $ throw "Boolean operators must have at least one argument"
    inferList⁺ArithExpr (x ∷ xs) = zipInference Theory._≟_ _∷_ (inferArithExpr x) (inferListArithExpr xs)
    
    inferListArithExpr : List B.ArithExpr → Inference (λ τ → List (ArithExpr Γ τ))
    inferListArithExpr []        = unknownType $ λ τ → return [] 
    inferListArithExpr (x ∷ xs) = zipInference Theory._≟_ _∷_ (inferArithExpr x) (inferListArithExpr xs)

  checkComparison :
    ({τ : ElementType} → ArithExpr Γ τ → ArithExpr Γ τ → CompExpr Γ τ) →
    B.ArithExpr →
    B.ArithExpr →
    TCM (Σ ElementType (CompExpr Γ))
  checkComparison f e₁ e₂ = do
    let inference = zipInference Theory._≟_ f (inferArithExpr e₁) (inferArithExpr e₂)
    case inference of λ where
      (unknownType _) → throw "unable to infer the type of the arithmetic expression"
      (knownType action) → action

  mutual
    checkBoolExpr : B.BoolExpr → TCM (BoolExpr Γ)
    checkBoolExpr (B.greaterThan  e₁ e₂) = comparison ∘ proj₂ <$> checkComparison greaterThan  e₁ e₂
    checkBoolExpr (B.lessThan     e₁ e₂) = comparison ∘ proj₂ <$> checkComparison lessThan     e₁ e₂
    checkBoolExpr (B.greaterEqual e₁ e₂) = comparison ∘ proj₂ <$> checkComparison greaterEqual e₁ e₂
    checkBoolExpr (B.lessEqual    e₁ e₂) = comparison ∘ proj₂ <$> checkComparison lessEqual    e₁ e₂
    checkBoolExpr (B.notEqual     e₁ e₂) = comparison ∘ proj₂ <$> checkComparison notEqual     e₁ e₂
    checkBoolExpr (B.equal        e₁ e₂) = comparison ∘ proj₂ <$> checkComparison equal        e₁ e₂
    checkBoolExpr (B.and es)    = and  <$> checkList⁺BoolExpr es
    checkBoolExpr (B.or  es)    = or   <$> checkList⁺BoolExpr  es
    
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
  equivalences' ← checkValidEquivalences networks'
  assertions' ← checkAssertions networks' assertions
  return (query networks' assertions' equivalences')

parseQuery : String → String ⊎ Query
parseQuery queryStr with B.parseQuery queryStr
... | B.Err.bad err = inj₁ (String.fromList err)
... | B.Err.ok untypedAST = checkQuery untypedAST
