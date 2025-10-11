module vnnlib-types where

open import Data.Rational as ℚ
open import Data.Bool

-- -- Element Types
data ElementType : Set where
  real         : ElementType
  float16      : ElementType
  float32      : ElementType
  float64      : ElementType
  bfloat16     : ElementType
  float8e4m3fn : ElementType
  float8e5m2   : ElementType
  float8e4m3fnuz : ElementType
  float8e5m2fnuz : ElementType
  float4e2m1   : ElementType
  int8         : ElementType
  int16        : ElementType
  int32        : ElementType
  int64        : ElementType
  uint8        : ElementType
  uint16       : ElementType
  uint32       : ElementType
  uint64       : ElementType

-- Add semantics for each type
ElementTypeToSet : ElementType → Set
ElementTypeToSet e = ℚ

isSameType : ElementType → ElementType → Bool
isSameType real real = true
isSameType float16 float16 = true
isSameType float32 float32 = true
isSameType float64 float64 = true
isSameType bfloat16 bfloat16 = true
isSameType float8e4m3fn float8e4m3fn = true
isSameType float8e5m2 float8e5m2 = true
isSameType float8e4m3fnuz float8e4m3fnuz = true
isSameType float8e5m2fnuz float8e5m2fnuz = true
isSameType float4e2m1 float4e2m1 = true
isSameType int8 int8 = true
isSameType int16 int16 = true
isSameType int32 int32 = true
isSameType int64 int64 = true
isSameType uint8 uint8 = true
isSameType uint16 uint16 = true
isSameType uint32 uint32 = true
isSameType uint64 uint64 = true
isSameType _ _ = false