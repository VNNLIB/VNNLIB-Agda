module vnnlib-normaliseQuery where

open import Reflection.AST
open import Agda.Builtin.Reflection
open import vnnlib-syntax using (Query)
open import vnnlib-semantics using (⟦_⟧𝕢)
open import Agda.Builtin.Unit using (⊤)

-- Define bind
_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
m >>= f = bindTC m f

-- Define sequencing
_>>_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
m >> m' = m >>= λ _ → m'

macro
  normaliseQuery : Query → Term → TC ⊤
  normaliseQuery query hole = do
    let 𝕢 = ⟦ query ⟧𝕢
    norm ← normalise (quoteTerm 𝕢)
    unify norm hole
