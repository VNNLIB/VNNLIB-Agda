open import ONNX.Syntax

module ONNX.Parser (theorySyntax : NetworkTheorySyntax) where

open import Data.Bool.Base
open import Data.String.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Relation.Binary.Definitions

open NetworkTheorySyntax theorySyntax

-- We unfortunately live in the real world so we have to define
-- an abstract interface to allow us to convert the tokens in the grammar
-- to various objects in the theory.
record NetworkTheoryParser : Set where
  field
    readElementType : String → Maybe ElementType
    readNumber : (τ : ElementType) → String → Maybe (TheoryTensor (tensorType τ []))
    readNodeOutputName : String → Maybe NodeOutputName
    
    _≟_ : DecidableEquality ElementType
