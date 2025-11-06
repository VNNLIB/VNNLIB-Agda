open import ONNX.Syntax

module VNNLIB.Theories
  (networkSyntax : NetworkTheorySyntax)
  where

open import VNNLIB.Theories.Definition networkSyntax public
open import VNNLIB.Theories.MultipleInputsOutputs networkSyntax public
