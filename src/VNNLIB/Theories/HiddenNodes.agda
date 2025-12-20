open import ONNX.Syntax

module VNNLIB.Theories.HiddenNodes
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.List using (length)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax

----------------
-- Theory set --
----------------

data HiddenNodes : Set where
  NH : HiddenNodes
  H  : HiddenNodes

---------
-- NH --
---------  

NoHiddenNodes : NetworkPredicate
NoHiddenNodes network = length (hiddenDeclarations network) ≡ 0

-- A query lives in the NH theory 
NoHiddenNodesTheory : Theory
NoHiddenNodesTheory (query networks _) = AllNetworks NoHiddenNodes networks


-------
-- H --
-------

-- Every query lives in the H theory
HiddenNodesTheory : Theory
HiddenNodesTheory = U

--------------------
-- Interpretation --
--------------------

instance
  HiddenNodesInterpretation : Interpretation HiddenNodes
  HiddenNodesInterpretation = record
    { interpretation = λ
      { NH → NoHiddenNodesTheory
      ; H  → HiddenNodesTheory
      }
    }

