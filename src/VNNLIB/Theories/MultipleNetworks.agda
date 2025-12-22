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
open import Data.Maybe using (just; nothing)


open import VNNLIB.Syntax networkSyntax
open import VNNLIB.Theories.Definition networkSyntax


NetworksPredicate : Set₁
NetworksPredicate = Pred NetworkContext 0ℓ

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
    networkContextLength : NetworkContext → ℕ
    networkContextLength [] = ℕ.zero
    networkContextLength (Γ ∷ x) = ℕ.suc (networkContextLength Γ)


-- A query that lives in the SNET theory
SingleNetworkTheory : Theory
SingleNetworkTheory (query networks _) = SingleNetwork networks

-----------
-- MENET --
-----------
data EqualNetwork : ∀ {Γ} → NetworkDeclaration Γ → Set where
  isEqualNetwork : ∀ {Γ name target inputs hidden outputs} → EqualNetwork {Γ} (declareNetwork name (just (equal-to target)) inputs hidden outputs)

data NotEqualNetwork : ∀ {Γ} → NetworkDeclaration Γ → Set where
  isEqualNetwork : ∀ {Γ name target inputs hidden outputs} → NotEqualNetwork {Γ} (declareNetwork name (just (equal-to target)) inputs hidden outputs)

-- A query where all networks are equal
MultipleEqualNetworks : NetworksPredicate
MultipleEqualNetworks [] = ⊥ -- TODO: sort out empty context
MultipleEqualNetworks (networks ∷ x) = NotEqualNetwork x × AllNetworks EqualNetwork networks

-- A query that lives in the MENET theory
MultipleEqualNetworksTheory : Theory
MultipleEqualNetworksTheory (query networks _) = MultipleEqualNetworks networks

-----------
-- MINET --
-----------
data IsomorphicNetwork : ∀ {Γ} → NetworkDeclaration Γ → Set where
  isIsomorphicNetwork : ∀ {Γ name target inputs hidden outputs} → IsomorphicNetwork {Γ} (declareNetwork name (just (isomorphic-to target)) inputs hidden outputs)

-- A network that is equal to another network is also in the isomorphic theory
MultipleIsomorphicNetworks : NetworksPredicate
MultipleIsomorphicNetworks [] = ⊥ -- TODO: sort out empty context
MultipleIsomorphicNetworks (networks ∷ x) = NotEqualNetwork x × AllNetworks TheoryIsomorphicNetwork networks
  where
    TheoryIsomorphicNetwork : NetworkPredicate
    TheoryIsomorphicNetwork network = IsomorphicNetwork network ⊎ EqualNetwork network

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
