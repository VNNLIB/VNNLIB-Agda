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
    readType : String → Maybe TheoryType
    readNumber : (τ : TheoryType) → String → Maybe (TheoryTensor (tensorType τ []))

    _≟_ : DecidableEquality TheoryType
