{-# OPTIONS --allow-unsolved-metas #-}
module context-isomorphism where

open import Data.Nat as ℕ
open import Data.List as List
open import Data.List.NonEmpty as List⁺ using (toList; List⁺)
open import Data.Fin
open import Function
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; subst; trans; module ≡-Reasoning; cong)
open Eq.≡-Reasoning
open import Data.List.Properties using (length-map)
open import Data.Product as Product using (proj₂; proj₁)
open import vnnlib-syntax as 𝐕
open import vnnlib-check-declarations
open import syntax-utils

open import utils

-- Proof that the length of the scope-checked declarations and the Syntax context are equivalent
length-Context : (Σ : List 𝐕.NetworkDefinition) → List.length Σ ≡ List.length (mkContext Σ)
length-Context Σ = sym (length-map convertNetworkΓ Σ)

open NetworkType
length-inputs :
  (Σ : List 𝐕.NetworkDefinition) →
  (n : Fin (List.length Σ)) →
  List.length (getInputDefs (List.lookup Σ n)) ≡ List.length (inputShapes&Types (List.lookup (mkContext Σ) (cast (length-Context Σ) n)))
length-inputs Σ n = {!!}

length-outputs :
  (Σ : List 𝐕.NetworkDefinition) →
  (n : Fin (List.length Σ)) →
  List.length (getOutputDefs (List.lookup Σ n)) ≡ List.length (outputShapes&Types (List.lookup (mkContext Σ) (cast (length-Context Σ) n)))
length-outputs Σ n = {!!}
