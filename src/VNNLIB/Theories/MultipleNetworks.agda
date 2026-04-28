open import ONNX.Syntax

module VNNLIB.Theories.MultipleNetworks
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product.Base using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (Pred; U)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level
open import Data.Maybe using (just; nothing)


open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax

----------------
-- Theory set --
----------------

data MultipleNetworks : Set where
  SNET  : MultipleNetworks
  MENET : MultipleNetworks
  MINET : MultipleNetworks
  MNET  : MultipleNetworks

----------
-- SNET --
----------  

SingleNetwork : NetworksPredicate
SingleNetwork networks = networkContextLength networks ≡ 1
  where
    networkContextLength : NetworkDeclarations → ℕ
    networkContextLength [] = ℕ.zero
    networkContextLength (x ∷ Γ) = ℕ.suc (networkContextLength Γ)
    
-- A query that lives in the SNET theory
SingleNetworkTheory : Theory
SingleNetworkTheory (query networks _ _) = SingleNetwork networks

-----------
-- MENET --
-----------

IsEqualNetwork : NetworkDeclaration → Set
IsEqualNetwork (declareNetwork _ _ _ _ (equal-to _)) = ⊤
IsEqualNetwork _ = ⊥

-- A query where all networks are equal
MultipleEqualNetworks : NetworksPredicate
MultipleEqualNetworks []        = ⊤
MultipleEqualNetworks (d ∷ ds) = All IsEqualNetwork ds

-- A query that lives in the MENET theory
MultipleEqualNetworksTheory : Theory
MultipleEqualNetworksTheory (query networks _ _) = MultipleEqualNetworks networks

-----------
-- MINET --
-----------

IsIsomorphicNetwork : NetworkDeclaration → Set
IsIsomorphicNetwork (declareNetwork _ _ _ _ (isomorphic-to _)) = ⊤
IsIsomorphicNetwork _ = ⊥

-- A network that is equal to another network is also in the isomorphic theory
MultipleIsomorphicNetworks : NetworksPredicate
MultipleIsomorphicNetworks []        = ⊤
MultipleIsomorphicNetworks (d ∷ ds) = All TheoryIsomorphicNetwork ds
  where
    TheoryIsomorphicNetwork : NetworkPredicate
    TheoryIsomorphicNetwork network = IsIsomorphicNetwork network ⊎ IsEqualNetwork network

-- A query that lives in the MINET theory
MultipleIsomorphicNetworksTheory : Theory
MultipleIsomorphicNetworksTheory (query networks _ _) = MultipleIsomorphicNetworks networks


----------
-- MNET --
----------

-- Every query lives in the MNET theory
MultipleNetworksTheory : Theory
MultipleNetworksTheory = U

--------------------
-- Interpretation --
--------------------

instance
   MultipleNetworksInterpretation : Interpretation MultipleNetworks
   MultipleNetworksInterpretation = record
     { interpretation = λ
       { SNET  → SingleNetworkTheory
       ; MENET → MultipleEqualNetworksTheory
       ; MINET → MultipleIsomorphicNetworksTheory
       ; MNET  → MultipleNetworksTheory
       }
     }
