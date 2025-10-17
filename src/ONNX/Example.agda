module ONNX.Example where

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.String.Base
open import Data.List.Base
open import Agda.Builtin.Float using (Float)
open import Level

open import tensor

open import ONNX.Syntax
open import ONNX.Semantics

----------------------------------------------------------------------------
-- Syntax
----------------------------------------------------------------------------

-- Types in the ONNX specification
data ONNXType : Set where
  float64        : ONNXType
  -- float16        : ONNXType
  -- float32        : ONNXType
  -- bfloat16       : ONNXType
  -- float8e4m3fn   : ONNXType
  -- float8e5m2     : ONNXType
  -- float8e4m3fnuz : ONNXType
  -- float8e5m2fnuz : ONNXType
  -- float4e2m1     : ONNXType
  -- int8           : ONNXType
  -- int16          : ONNXType
  -- int32          : ONNXType
  -- int64          : ONNXType
  -- uint8          : ONNXType
  -- uint16         : ONNXType
  -- uint32         : ONNXType
  -- uint64         : ONNXType

-- Equivalence between two ONNX types
_==_ : ONNXType → ONNXType → Bool
float64 == float64 = true

ONNXTensor : TensorSignature ONNXType → Set
ONNXTensor (tensorSig float64 shape) = Tensor Float shape

data ONNXOperator : InputsSignature ONNXType → OutputsSignature ONNXType → Set where
  constant : ∀ {sig} → ONNXTensor sig → ONNXOperator [] (sig ∷ [])
  add : ∀ {sig} → ONNXOperator (sig ∷ sig ∷ []) (sig ∷ [])

data ONNXNetwork : NetworkSignature ONNXType → Set where
  input : ∀ inputSig → ONNXNetwork (networkSig inputSig inputSig)

parseConstant : (τ : ONNXType) → String → Maybe (ONNXTensor (tensorSig τ []))
parseConstant float64 s = {!!}

exampleSyntax : ONNXSyntax
exampleSyntax = record
  { ONNXType = ONNXType
  ; ONNXBool = {!!}
  ; ONNXTensor = ONNXTensor
  ; ONNXNetwork = ONNXNetwork
  ; parseConstant = parseConstant
  }

----------------------------------------------------------------------------
-- Example semantics
----------------------------------------------------------------------------

⟦_⟧type : ONNXType → Set
⟦ float64 ⟧type = Float

⟦_⟧tensor : ∀ {sig} → ONNXTensor sig → TensorSemantics ⟦_⟧type sig
⟦_⟧tensor {tensorSig float64 shape} tensor = tensor

⟦constant⟧ : ∀ {sig} → ONNXTensor sig → {!!}
⟦constant⟧ = {!!}

⟦add⟧ : ∀ {sig} → ONNXTensor sig → {!!}
⟦add⟧ = {!!}

⟦_⟧network : ∀ {sig} → ONNXNetwork sig → NetworkSemantics ⟦_⟧type sig
⟦_⟧network = {!!}

⟦_⟧neg : ∀ (τ : ONNXType) → TensorOp1 ⟦ τ ⟧type ⟦ τ ⟧type
⟦ float64 ⟧neg = {!!}

⟦_⟧add : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type ⟦ τ ⟧type
⟦ float64 ⟧add = {!!}

⟦_⟧mul : ∀ (τ : ONNXType) → TensorOp2 ⟦ τ ⟧type ⟦ τ ⟧type ⟦ τ ⟧type
⟦ float64 ⟧mul = {!!}

exampleSemantics : ONNXSemantics exampleSyntax
exampleSemantics = record
  { ⟦_⟧type    = ⟦_⟧type
  ; ⟦_⟧tensor  = ⟦_⟧tensor
  ; ⟦_⟧network = ⟦_⟧network
  ; ⟦_⟧neg     = ⟦_⟧neg
  ; ⟦_⟧add     = ⟦_⟧add
  ; ⟦_⟧mul     = ⟦_⟧mul
  }
