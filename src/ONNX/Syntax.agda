module ONNX.Syntax where

open import Data.Bool.Base
open import Data.List.Base
open import Data.String.Base
open import Data.Maybe.Base
open import Level
open import tensor using (TensorShape)

-- A signature for a tensor
record TensorSignature (Types : Set) : Set where
  constructor tensorSig
  field
    tensorType : Types
    tensorDims : TensorShape

InputsSignature : (Types : Set) → Set
InputsSignature Types = List (TensorSignature Types)

OutputsSignature : (Types : Set) → Set
OutputsSignature Types = List (TensorSignature Types)

-- A signature for a network
record NetworkSignature (Types : Set) : Set where
  constructor networkSig
  field
    inputs : InputsSignature Types
    outputs : OutputsSignature Types

-- An implementation of the subset of syntax of ONNX neccessary to define
-- the syntax of VNN-LIB.
record ONNXSyntax : Set₁ where
  field
    -- The set of types in the ONNX specification
    ONNXType : Set

    -- We must have the boolean type
    ONNXBool : ONNXType

    -- The internal ONNX representation of tensors
    ONNXTensor : TensorSignature ONNXType → Set

    -- The internal ONNX representation of networks
    ONNXNetwork : NetworkSignature ONNXType → Set

    -- A method of parsing strings into zero-dimensaional ONNX tensors (i.e. a constant)
    parseConstant : (τ : ONNXType) → String → Maybe (ONNXTensor (tensorSig τ []))
