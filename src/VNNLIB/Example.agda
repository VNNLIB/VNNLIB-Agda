module vnnlib-semantics-demo where

open import Data.String using (String; fromList)
open import Data.Nat
open import Data.Bool
open import Data.Product using (_,_)
open import Data.Rational
open import Data.Fin
open import Data.List.Relation.Unary.Any using (Any;here)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)
open import Agda.Builtin.Int
open import Data.Integer.Base
open import Data.List.Base
open import Data.Sign.Base
open import Level using (0ℓ)
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Data.Empty using (⊥)

open import Syntax.Parser using (Err; parseQuery)
open import Syntax.AST as AST using (Query)

open import tensor
open import vnnlib-semantics
open import vnnlib-types
open import vnnlib-syntax as VNN
open import vnnlib-check

small_vcl_query : String
small_vcl_query = " (vnnlib-version <2.0>)
(declare-network N1
	(declare-input X Real [3])
	(declare-output Y Real [])
)
(assert (and (<= 0 X[0]) (>= 1 X[0])))
(assert (<= 0 Y[0]))
"

-- query = mkQuery
--   (declareNetwork (SVariableName "N1")
--     (declareInput (SVariableName "X") real (3 ∷ []) ∷ [])
--     (declareOutput (SVariableName "Y") real [] ∷ []) ∷ [])
--   (assert
--     (andExpr
--       (compExpr (real , lessEqual (constant 0ℚ) (varInput zero (here refl) (non-empty zero tensor.empty))) ∷
--       (compExpr (real , greaterEqual (constant 1ℚ) (varInput zero (here refl) (non-empty zero tensor.empty)))) ∷ []))
--    ∷
--    assert (compExpr (real , lessEqual (constant 0ℚ) (varOutput zero (here refl) tensor.empty)))
--    ∷ [])

-- Expected semantics for the small_vcl_query
𝕢 : Set
𝕢 = (n
 : (i : Fin 1) →
   ({τ : ElementType} {shape : List ℕ}
    (j
     : Any (_≡_ (shape , τ))
       (NetworkType.inputShapes&Types
        (Data.List.Base.lookup
         (networkType ((3 ∷ [] , real) ∷ []) (([] , real) ∷ []) ∷ []) i))) →
    Tensor (ElementTypeToSet τ) shape) →
   {τ : ElementType} {shape : List ℕ}
   (j
    : Any (_≡_ (shape , τ))
      (NetworkType.outputShapes&Types
       (Data.List.Base.lookup
        (networkType ((3 ∷ [] , real) ∷ []) (([] , real) ∷ []) ∷ []) i))) →
   Tensor (ElementTypeToSet τ) shape) →
 Data.Product.Σ
 ((i : Fin 1) {τ : ElementType} {shape : List ℕ}
   (j
   : Any (_≡_ (shape , τ))
     (NetworkType.inputShapes&Types
       (Data.List.Base.lookup
       (networkType ((3 ∷ [] , real) ∷ []) (([] , real) ∷ []) ∷ []) i))) →
 Tensor (ElementTypeToSet τ) shape)
 (λ x →
   (((Agda.Builtin.Int.Int.pos 0 Data.Integer.Base.≤ᵇ
      ((Data.Integer.Base.sign
        (↥
         tensorLookup (non-empty zero TensorIndices.empty)
         (x zero (here refl)))
        Data.Sign.Base.* Data.Sign.Base.Sign.+)
       Data.Integer.Base.◃
       (Data.Integer.Base.∣
        ↥
        tensorLookup (non-empty zero TensorIndices.empty)
        (x zero (here refl))
        ∣
        Data.Nat.* 1)))
     ∧
     (((Data.Integer.Base.sign
        (↥
         tensorLookup (non-empty zero TensorIndices.empty)
         (x zero (here refl)))
        Data.Sign.Base.* Data.Sign.Base.Sign.+)
       Data.Integer.Base.◃
       (Data.Integer.Base.∣
        ↥
        tensorLookup (non-empty zero TensorIndices.empty)
        (x zero (here refl))
        ∣
        Data.Nat.* 1))
      Data.Integer.Base.≤ᵇ
      Agda.Builtin.Int.Int.pos
      (ℕ.suc
       (ℚ.denominator-1
        (tensorLookup (non-empty zero TensorIndices.empty)
         (x zero (here refl)))
        Data.Nat.+ 0)))
     ∧ true)
    ∧ true)
   ∧
   (Agda.Builtin.Int.Int.pos 0 Data.Integer.Base.≤ᵇ
    ((Data.Integer.Base.sign
      (↥ tensorLookup TensorIndices.empty (n zero (x zero) (here refl)))
      Data.Sign.Base.* Data.Sign.Base.Sign.+)
     Data.Integer.Base.◃
     (Data.Integer.Base.∣
      ↥ tensorLookup TensorIndices.empty (n zero (x zero) (here refl)) ∣
      Data.Nat.* 1)))
   ∧ true
   ≡ true)


checkedQuery : Result VNN.Query
checkedQuery with parseQuery small_vcl_query
... | Err.ok x = check x
... | Err.bad x = error (fromList x)

checkSemantics : Result VNN.Query → {!!}
checkSemantics with checkedQuery
... | error x = {!!}
... | success y = {!!}
  where
    comp = ⟦ y ⟧𝕢
    c : comp ≡ 𝕢
    c = {!!}
