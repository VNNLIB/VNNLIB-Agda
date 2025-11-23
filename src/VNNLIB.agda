open import ONNX.Syntax
open import ONNX.Semantics

module VNNLIB
  (onnxSyntax : NetworkTheorySyntax)
  (onnxSemantics : NetworkTheorySemantics onnxSyntax)
  where

open import Data.Sum.Base

open import VNNLIB.Syntax
open import VNNLIB.Semantics
open import VNNLIB.Parser
open import VNNLIB.Theories

------------
-- VNNLIB --
------------

VNNLIBQuery : Set
VNNLIBQuery = Query onnxSyntax

⟦VNNLIBQuery⟧ : QuerySemantics onnxSemantics
⟦VNNLIBQuery⟧ = ⟦query⟧ onnxSemantics

-----------------------
-- VNNLIB over reals --
-----------------------

open import ONNX.Real onnxSyntax onnxSemantics
  using (realSyntax; realSemantics; RealNetworkSemantics)

RealVNNLIBQuery : Set
RealVNNLIBQuery = Query realSyntax

⟦RealVNNLIBQuery⟧ : (realNetworkSemantics : RealNetworkSemantics) → QuerySemantics (realSemantics realNetworkSemantics)
⟦RealVNNLIBQuery⟧ realNetworkSemantics = ⟦query⟧ (realSemantics realNetworkSemantics)
