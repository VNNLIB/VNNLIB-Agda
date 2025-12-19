open import ONNX.Syntax

module VNNLIB.Theories.MultipleNetworks
  (networkSyntax : NetworkTheorySyntax)
  where

open import Data.Nat using (ℕ)
open import Data.Unit.Base using (⊤)
open import Data.Empty using (⊥)
open import Data.List using (length)
open import Data.Product.Base using (_×_)
open import Data.Sum using (_⊎_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level


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


NetworksPredicate : Set₁
NetworksPredicate = Pred NetworkContext 0ℓ


----------
-- SNET --
----------  

networkContextLength : NetworkContext → ℕ
networkContextLength [] = ℕ.zero
networkContextLength (Γ ∷ x) = ℕ.suc (networkContextLength Γ)

SingleNetwork : NetworksPredicate
SingleNetwork networks = networkContextLength networks ≡ 1

-- A query that lives in the SNET theory
SingleNetworkTheory : Theory
SingleNetworkTheory (query networks _) = SingleNetwork networks

-----------
-- MENET --
-----------

-- A network has been declared as equal to another network
EqualNetwork : NetworkPredicate
EqualNetwork (declareNetwork _ _ _ _ none) = ⊥
EqualNetwork (declareNetwork _ _ _ _ (equal-to x)) = ⊤
EqualNetwork (declareNetwork _ _ _ _ (isomorphic-to x)) = ⊥

-- A network has not been declared as congruent to another network
NotCongruentNetwork : NetworkPredicate
NotCongruentNetwork (declareNetwork _ _ _ _ none) = ⊤
NotCongruentNetwork (declareNetwork _ _ _ _ (equal-to x)) = ⊥ 
NotCongruentNetwork (declareNetwork _ _ _ _ (isomorphic-to x)) = ⊥

-- A query where all networks are equal
MultipleEqualNetworks : NetworksPredicate
MultipleEqualNetworks [] = ⊥
MultipleEqualNetworks (Γ ∷ d) with Γ
... | []         = NotCongruentNetwork d
... | (Γ' ∷ d') = EqualNetwork d × MultipleEqualNetworks (Γ' ∷ d')

-- A query that lives in the SNET theory
MultipleEqualNetworksTheory : Theory
MultipleEqualNetworksTheory (query networks _) = MultipleEqualNetworks networks

-----------
-- MINET --
-----------

-- A network has been declared as isomorphic to another network
IsomorphicNetwork : NetworkPredicate
IsomorphicNetwork (declareNetwork _ _ _ _ none) = ⊥
IsomorphicNetwork (declareNetwork _ _ _ _ (equal-to x)) = ⊥
IsomorphicNetwork (declareNetwork _ _ _ _ (isomorphic-to x)) = ⊤

-- A network that is equal to another network is also in the isomorphic theory
MultipleIsomorphicNetworks : NetworksPredicate
MultipleIsomorphicNetworks [] = ⊥
MultipleIsomorphicNetworks (Γ ∷ d) with Γ
... | []         = NotCongruentNetwork d
... | (Γ' ∷ d') = IsomorphicNetwork d × (MultipleIsomorphicNetworks (Γ' ∷ d') ⊎ AllEqualNetworks (Γ' ∷ d'))
  where
    AllEqualNetworks : NetworksPredicate
    AllEqualNetworks []        = ⊤
    AllEqualNetworks (Γ ∷ d)  = EqualNetwork d × AllEqualNetworks Γ

-- A query that lives in the MINET theory
MultipleIsomorphicNetworksTheory : Theory
MultipleIsomorphicNetworksTheory (query networks _) = MultipleIsomorphicNetworks networks


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
