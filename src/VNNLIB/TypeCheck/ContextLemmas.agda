module VNNLIB.TypeCheck.ContextLemmas where

open import Data.Nat as ℕ
open import Data.List as List
open import Data.Fin
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; module ≡-Reasoning; cong)
open Eq.≡-Reasoning
open import Data.List.Properties using (length-map)
open import VNNLIB.Syntax
open import Data.RationalUtils
open import Data.FloatUtils

lookup-map : {A B : Set} → (f : A → B) → (xs : List A) → (i : Fin (length xs)) → lookup (map f xs) (cast (sym (length-map f xs)) i) ≡ f (lookup xs i)
lookup-map f (x ∷ a) zero = refl
lookup-map f (x ∷ a) (suc b) = lookup-map f a b

-- Proof that the length of the scope-checked declarations and the Syntax context are equivalent
length-Context : (Σ : List NetworkDefinition) → List.length Σ ≡ List.length (mkContext Σ)
length-Context Σ = sym (length-map convertNetworkΓ Σ)

-- Proofs that the length of the Input and Output definitions are the same as in the Context
open NetworkType
length-inputs :
  (Σ : List NetworkDefinition) →
  (n : Fin (length Σ)) →
  List.length (getInputDefs (List.lookup Σ n)) ≡ List.length (inputShapes&Types (List.lookup (mkContext Σ) (cast (length-Context Σ) n)))
length-inputs Σ n = begin
    length (getInputDefs (lookup Σ n))                               ≡⟨ sym (length-map convertInputΓ (getInputDefs (lookup Σ n))) ⟩
    length (map convertInputΓ (getInputDefs (lookup Σ n)))           ≡⟨ cong length (helper Σ n) ⟩
    length (inputShapes&Types (lookup (mkContext Σ) (cast (length-Context Σ) n)))
  ∎
  where
    helper : ∀ Σ n →  map convertInputΓ (getInputDefs (lookup Σ n)) ≡ inputShapes&Types (lookup (mkContext Σ) (cast (length-Context Σ) n))
    helper Σ n rewrite lookup-map convertNetworkΓ Σ n = refl

length-outputs :
  (Σ : List NetworkDefinition) →
  (n : Fin (List.length Σ)) →
  List.length (getOutputDefs (List.lookup Σ n)) ≡ List.length (outputShapes&Types (List.lookup (mkContext Σ) (cast (length-Context Σ) n)))
length-outputs Σ n = begin
    length (getOutputDefs (lookup Σ n))                               ≡⟨ sym (length-map convertOutputΓ (getOutputDefs (lookup Σ n))) ⟩
    length (map convertOutputΓ (getOutputDefs (lookup Σ n)))          ≡⟨ cong length (helper Σ n) ⟩
    length (outputShapes&Types (lookup (mkContext Σ) (cast (length-Context Σ) n)))
  ∎
  where
    helper : ∀ Σ n →  map convertOutputΓ (getOutputDefs (lookup Σ n)) ≡ outputShapes&Types (lookup (mkContext Σ) (cast (length-Context Σ) n))
    helper Σ n rewrite lookup-map convertNetworkΓ Σ n = refl
