module vnnlib-semantics where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Fin as Fin
open import Data.Product as Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Data.Empty using (⊥)
open import Agda.Builtin.Float

open import utils
open import vnnlib-types
open import vnnlib-syntax
open import tensor using (Tensor; TensorShape; tensorLookup)

    
-- Network Implementation Representation
SetOfTensors : List (TensorShape × ElementType) → Set 
SetOfTensors tensorsInfo =
  (i : Fin (List.length tensorsInfo)) → let shape&type = List.lookup tensorsInfo i in Tensor (ElementTypeToSet (proj₂ shape&type)) (proj₁ shape&type) 

NetworkImplementation : NetworkType → Set
NetworkImplementation networkτ = SetOfTensors inputs → SetOfTensors outputs
  where
    inputs = NetworkType.inputShapes&Types networkτ
    outputs = NetworkType.outputShapes&Types networkτ

-- Environment Representation
Assignments : Context → Set
Assignments Γ = 
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in SetOfTensors (NetworkType.inputShapes&Types networkType)

NetworkImplementations : Context → Set
NetworkImplementations Γ = 
  (i : Fin (List.length Γ)) → let networkType = List.lookup Γ i in NetworkImplementation networkType

Environment : Context → Set
Environment Γ = NetworkImplementations Γ × Assignments Γ

-- Semantics of Assertions
module _ (Γ : Context) (ε : Environment Γ) where

  module _ (τ : ElementType) where
    postulate ⟦_⟧ₐ : ArithExpr Γ τ → ElementTypeToSet τ
    postulate ⟦_⟧ᶜ : CompExpr Γ τ → Bool
   
    ⟦_⟧realₐ : ArithExpr Γ real → ℚ
    ⟦ (constant a) ⟧realₐ        = a
    ⟦ (negate a) ⟧realₐ           = 0ℚ ℚ.- ⟦ a ⟧realₐ
    ⟦ (varInput iₙₑₜ jᵢₙₚ indices) ⟧realₐ = tensorLookup indices {!(((proj₂ ε) iₙₑₜ) jᵢₙₚ)!} -- (((proj₂ ε) iₙₑₜ) jᵢₙₚ)
    ⟦ (varOutput iₙₑₜ jₒᵤₜ indices) ⟧realₐ = tensorLookup indices {!!} -- (((((proj₁ ε) iₙₑₜ) (((proj₂ ε) iₙₑₜ))) jₒᵤₜ))
    ⟦ (add []) ⟧realₐ             = 0ℚ
    ⟦ (add (a₀ ∷ a)) ⟧realₐ       = ⟦ a₀ ⟧realₐ ℚ.+ ⟦ (add a) ⟧realₐ
    ⟦ (mult []) ⟧realₐ            = 1ℚ
    ⟦ (mult (a₀ ∷ a)) ⟧realₐ      = ⟦ a₀ ⟧realₐ ℚ.* ⟦ (mult a) ⟧realₐ
    ⟦ (minus []) ⟧realₐ           = 0ℚ
    ⟦ (minus (a₀ ∷ a)) ⟧realₐ     = ⟦ a₀ ⟧realₐ ℚ.- ⟦ (add a) ⟧realₐ

    ⟦_⟧realᶜ : CompExpr Γ real → Bool
    ⟦ greaterThan x x₁ ⟧realᶜ = ⟦ x ⟧realₐ Real.>ᵇ ⟦ x₁ ⟧realₐ
    ⟦ lessThan x x₁ ⟧realᶜ = ⟦ x ⟧realₐ Real.<ᵇ ⟦ x₁ ⟧realₐ
    ⟦ greaterEqual x x₁ ⟧realᶜ = ⟦ x ⟧realₐ Real.≥ᵇ ⟦ x₁ ⟧realₐ
    ⟦ lessEqual x x₁ ⟧realᶜ = ⟦ x ⟧realₐ ℚ.≤ᵇ ⟦ x₁ ⟧realₐ
    ⟦ notEqual x x₁ ⟧realᶜ = ⟦ x ⟧realₐ Real.≠ᵇ ⟦ x₁ ⟧realₐ
    ⟦ equal x x₁ ⟧realᶜ = ⟦ x ⟧realₐ Real.=ᵇ ⟦ x₁ ⟧realₐ

    ⟦_⟧float64ₐ : ArithExpr Γ float64 → Float
    ⟦ (constant a) ⟧float64ₐ        = a
    ⟦ (negate a) ⟧float64ₐ           = primFloatMinus 0.0 ⟦ a ⟧float64ₐ
    ⟦ (varInput iₙₑₜ jᵢₙₚ indices ) ⟧float64ₐ = tensorLookup indices {!!} -- tensorLookup indices (((proj₂ ε) iₙₑₜ) jᵢₙₚ)
    ⟦ (varOutput iₙₑₜ jₒᵤₜ indices ) ⟧float64ₐ = tensorLookup indices {!!} -- tensorLookup indices (((((proj₁ ε) iₙₑₜ) (((proj₂ ε) iₙₑₜ))) jₒᵤₜ))
    ⟦ (add []) ⟧float64ₐ             = 0.0
    ⟦ (add (a₀ ∷ a)) ⟧float64ₐ       = primFloatPlus ⟦ a₀ ⟧float64ₐ ⟦ (add a) ⟧float64ₐ
    ⟦ (mult []) ⟧float64ₐ            = 1.0
    ⟦ (mult (a₀ ∷ a)) ⟧float64ₐ      = primFloatTimes ⟦ a₀ ⟧float64ₐ ⟦ (mult a) ⟧float64ₐ
    ⟦ (minus []) ⟧float64ₐ           = 0.0
    ⟦ (minus (a₀ ∷ a)) ⟧float64ₐ     = primFloatMinus ⟦ a₀ ⟧float64ₐ  ⟦ (add a) ⟧float64ₐ

    ⟦_⟧float64ᶜ : CompExpr Γ float64 → Bool
    ⟦ greaterThan x x₁ ⟧float64ᶜ = ⟦ x ⟧float64ₐ Float64.>ᵇ ⟦ x₁ ⟧float64ₐ
    ⟦ lessThan x x₁ ⟧float64ᶜ = ⟦ x ⟧float64ₐ Float64.<ᵇ ⟦ x₁ ⟧float64ₐ
    ⟦ greaterEqual x x₁ ⟧float64ᶜ = ⟦ x ⟧float64ₐ Float64.≥ᵇ ⟦ x₁ ⟧float64ₐ
    ⟦ lessEqual x x₁ ⟧float64ᶜ = ⟦ x ⟧float64ₐ Float64.≤ᵇ ⟦ x₁ ⟧float64ₐ
    ⟦ notEqual x x₁ ⟧float64ᶜ = ⟦ x ⟧float64ₐ Float64.≠ᵇ ⟦ x₁ ⟧float64ₐ
    ⟦ equal x x₁ ⟧float64ᶜ = ⟦ x ⟧float64ₐ Float64.=ᵇ ⟦ x₁ ⟧float64ₐ

  ⟦_⟧ᵇ : BoolExpr Γ → Bool
  ⟦ (literal b) ⟧ᵇ          = b
  ⟦ compExpr (real , snd) ⟧ᵇ = ⟦ real ⟧realᶜ snd
  ⟦ compExpr (float64 , snd) ⟧ᵇ = ⟦ float64 ⟧float64ᶜ snd
  ⟦ compExpr (fst , snd) ⟧ᵇ = ⟦ fst ⟧ᶜ snd
  ⟦ (andExpr []) ⟧ᵇ         = true
  ⟦ (andExpr (b ∷ xb)) ⟧ᵇ   = _∧_ ⟦ b ⟧ᵇ ⟦ (andExpr xb) ⟧ᵇ
  ⟦ (orExpr []) ⟧ᵇ          = false
  ⟦ (orExpr (b ∷ xb)) ⟧ᵇ    = _∨_ ⟦ b ⟧ᵇ ⟦  (orExpr xb) ⟧ᵇ

  ⟦_⟧ₚ : Assertion Γ → Bool
  ⟦ (assert p) ⟧ₚ = ⟦ p ⟧ᵇ

-- Semantics of a Query
⟦_⟧𝕢 : Query → Set
⟦ mkQuery networks assertions ⟧𝕢 =
  let Γ = mkContext networks in (n : NetworkImplementations Γ) → ∃ λ (x : Assignments Γ) → List.foldl (λ z z₁ → and (z ∷ ⟦ Γ ⟧ₚ (n , x) z₁ ∷ [])) true assertions ≡ true



