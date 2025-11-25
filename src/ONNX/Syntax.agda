module ONNX.Syntax where

open import Data.Bool.Base
open import Data.List.Base
open import Data.List.NonEmpty.Base
open import Data.String.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Level
open import Data.Tensor using (TensorShape)
open import Data.List.NonEmpty.Relation.Unary.All using () renaming (All to All⁺)

-- A signature for a tensor
record TensorType (Types : Set) : Set where
  constructor tensorType
  field
    tensorType : Types
    tensorDims : TensorShape

InputTypes : (Types : Set) → Set
InputTypes Types = List⁺ (TensorType Types)

HiddenNodeTypes : (Types : Set) → Set
HiddenNodeTypes Types = List (TensorType Types)

OutputTypes : (Types : Set) → Set
OutputTypes Types = List⁺ (TensorType Types)

-- A signature for a network
record NetworkType (Types : Set) : Set where
  constructor networkType
  field
    inputs : InputTypes Types
    outputs : OutputTypes Types


-- An implementation of the subset of syntax of ONNX necessary to define
-- the syntax of VNN-LIB.
record NetworkTheorySyntax : Set₁ where
  field
    -- The set of types in the ONNX specification
    ElementType : Set

    -- The internal ONNX representation of tensors
    TheoryTensor : TensorType ElementType → Set

    -- The internal ONNX representation of networks
    Model : NetworkType ElementType → Set

    -- A pointer to a node in the network with a given type. 
    Node : ∀ {γ} → Model γ → TensorType ElementType → Set

    -- A function that returns the input nodes of a network
    inputNodes : ∀ {γ} (n : Model γ) → All⁺ (Node n) (NetworkType.inputs γ)
    
    -- A function that returns the output nodes of a network
    outputNodes : ∀ {γ} (n : Model γ) → All⁺ (Node n) (NetworkType.outputs γ)

    -- The set of allowable names for the output tensors of nodes inside of networks
    NodeOutputName : Set
    
    -- A judgement that a network contains a node of with an output of a given name
    NodeHasOutput : ∀ {γ} {n : Model γ} {δ} → Node n δ → NodeOutputName → Set 
