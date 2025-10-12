module vnnlib-types where

open import Data.Rational as ℚ
open import Data.Bool
open import Agda.Builtin.Float using (Float)
open import Data.String using (String)
open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_;refl)

-- -- Element Types
data ElementType : Set where
  real         : ElementType
  float64      : ElementType
  -- float16      : ElementType
  -- float32      : ElementType
  -- bfloat16     : ElementType
  -- float8e4m3fn : ElementType
  -- float8e5m2   : ElementType
  -- float8e4m3fnuz : ElementType
  -- float8e5m2fnuz : ElementType
  -- float4e2m1   : ElementType
  -- int8         : ElementType
  -- int16        : ElementType
  -- int32        : ElementType
  -- int64        : ElementType
  -- uint8        : ElementType
  -- uint16       : ElementType
  -- uint32       : ElementType
  -- uint64       : ElementType


-- Set mapping for each supported Element type
-- Used in vnnlib-syntax
ElementTypeToSet : ElementType → Set
ElementTypeToSet real = ℚ
ElementTypeToSet float64 = Float

-- Equivalence between two element types
_≡ᴱᵀ_ : (τ₁ : ElementType) → (τ₂ : ElementType) → Result (τ₁ ≡ τ₂)
real ≡ᴱᵀ real = success refl
real ≡ᴱᵀ float64 = error "Type mismatch"
float64 ≡ᴱᵀ real = error "Type mismatch"
float64 ≡ᴱᵀ float64 = success refl
