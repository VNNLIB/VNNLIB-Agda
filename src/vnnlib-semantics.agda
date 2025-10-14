module vnnlib-semantics where

open import Data.List as List
open import Data.String hiding (map)
open import Data.Rational as ℚ
open import Data.Bool
open import Data.Fin as Fin
open import Data.Product as Product
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Agda.Builtin.Float

open import utils
open import vnnlib-types
open import vnnlib-syntax
open import tensor

private
  variable
    τ : ElementType
    shape : TensorShape

-- Semantics of Assertions
module _ (Γ : Context) where

  -- Network Implementation Representation
  InputTensor : (i : NetworkRef Γ) → InputRef Γ i τ shape → Set
  InputTensor  {τ} {shape} i j = Tensor (ElementTypeToSet τ) shape

  InputTensors : (i : NetworkRef Γ) → Set
  InputTensors i = ∀ {τ} {shape} (j : InputRef Γ i τ shape) → InputTensor i j

  OutputTensor : (i : NetworkRef Γ) → OutputRef Γ i τ shape → Set
  OutputTensor {τ} {shape} i j = Tensor (ElementTypeToSet τ) shape

  OutputTensors : (i : NetworkRef Γ) → Set
  OutputTensors i = ∀ {τ} {shape} (j : OutputRef Γ i τ shape) → OutputTensor i j

  NetworkImplementation : NetworkRef Γ → Set
  NetworkImplementation i = InputTensors i → OutputTensors i

  -- Environment Representation
  Assignments : Set
  Assignments = (i : NetworkRef Γ) → InputTensors i

  NetworkImplementations : Set
  NetworkImplementations = (i : NetworkRef Γ) → NetworkImplementation i

  Environment : Set
  Environment = NetworkImplementations × Assignments

  module _ (ε : Environment) where
    -- Semantics for real --
    ⟦_⟧realₐ : ArithExpr Γ real → ℚ
    ⟦ (constant a) ⟧realₐ        = a
    ⟦ (negate a) ⟧realₐ           = 0ℚ ℚ.- ⟦ a ⟧realₐ
    ⟦ (varInput i j indices) ⟧realₐ = tensorLookup indices (proj₂ ε i j)
    ⟦ (varOutput i j indices) ⟧realₐ = tensorLookup indices ((proj₁ ε i) (proj₂ ε i) j)
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
    
    -- Semantics for float64 --
    ⟦_⟧float64ₐ : ArithExpr Γ float64 → Float
    ⟦ (constant a) ⟧float64ₐ        = a
    ⟦ (negate a) ⟧float64ₐ           = primFloatMinus 0.0 ⟦ a ⟧float64ₐ
    ⟦ (varInput i j indices ) ⟧float64ₐ = tensorLookup indices (proj₂ ε i j)
    ⟦ (varOutput i j indices) ⟧float64ₐ = tensorLookup indices ((proj₁ ε i) (proj₂ ε i) j)
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
    ⟦ compExpr (real , snd) ⟧ᵇ = ⟦ snd ⟧realᶜ
    ⟦ compExpr (float64 , snd) ⟧ᵇ = ⟦ snd ⟧float64ᶜ
--    ⟦ compExpr (fst , snd) ⟧ᵇ = ⟦ fst ⟧ᶜ snd
    ⟦ (andExpr []) ⟧ᵇ         = true
    ⟦ (andExpr (b ∷ xb)) ⟧ᵇ   = _∧_ ⟦ b ⟧ᵇ ⟦ (andExpr xb) ⟧ᵇ
    ⟦ (orExpr []) ⟧ᵇ          = false
    ⟦ (orExpr (b ∷ xb)) ⟧ᵇ    = _∨_ ⟦ b ⟧ᵇ ⟦  (orExpr xb) ⟧ᵇ

    ⟦_⟧ₚ : Assertion Γ → Bool
    ⟦ (assert p) ⟧ₚ = ⟦ p ⟧ᵇ

-- Semantics of a Query
⟦_⟧𝕢 : Query → Set
⟦ mkQuery networks assertions ⟧𝕢 =
  let Γ = mkContext networks in (n : NetworkImplementations Γ) → ∃ λ (x : Assignments Γ) → 
              List.foldl (λ z z₁ → and (z ∷ ⟦ Γ ⟧ₚ (n , x) z₁ ∷ [])) true assertions ≡ true

