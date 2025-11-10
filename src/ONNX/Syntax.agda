module ONNX.Syntax where

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.NonEmpty.Base
open import Data.String.Base
open import Data.Maybe.Base
open import Level
open import Data.Tensor using (TensorShape)

-- A signature for a tensor
record TensorType (Types : Set) : Set where
  constructor tensorType
  field
    tensorType : Types
    tensorDims : TensorShape

InputTypes : (Types : Set) → Set
InputTypes Types = List⁺ (TensorType Types)

OutputTypes : (Types : Set) → Set
OutputTypes Types = List⁺ (TensorType Types)

-- A signature for a network
record NetworkType (Types : Set) : Set where
  constructor networkType
  field
    inputs : InputTypes Types
    outputs : OutputTypes Types

-- An implementation of the subset of syntax of ONNX neccessary to define
-- the syntax of VNN-LIB.
record NetworkTheorySyntax : Set₁ where
  field
    -- The set of types in the ONNX specification
    TheoryType : Set

    -- The internal ONNX representation of tensors
    TheoryTensor : TensorType TheoryType → Set

    -- The internal ONNX representation of networks
    TheoryNetwork : NetworkType TheoryType → Set
