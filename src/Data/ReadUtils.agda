module Data.ReadUtils where

--- Parsing various numerical constants ---

open import Data.Bool
open import Data.Bool.ListAction
open import Data.String as String using (String; _++_)
open import Data.List hiding (all)
open import Data.Nat as ℕ
open import Data.Integer as ℤ
open import Data.Nat.Properties using (m*n≢0)
open import Data.Char as Char using (Char; isDigit)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; case_of_)
open import Data.Product
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality.Core using (_≢_)
open import Data.List.Relation.Unary.Any as RUAny
open import Relation.Nullary
open import Data.Nat.Show
open import Data.Nat.Show as ℕshow using (show)
open import Data.Rational as ℚ
open import Data.Real
open import Data.Float.Base as Float using (Float)
open import Level

open import Effect.Monad
open import Data.Maybe.Effectful

open RawMonad (monad {0ℓ})

open import VNNLIB.Syntax.AST as 𝐁 hiding (String)

^-nonZero : ∀ m n → .{{ℕ.NonZero m}} → ℕ.NonZero (m ℕ.^ n)
^-nonZero m zero           = _
^-nonZero m (suc n) {{nz}} = m*n≢0 m (m ℕ.^ n) {{nz}} {{^-nonZero m n}} 

readℕ₁₀ : String → Maybe ℕ
readℕ₁₀ n = readMaybe 10 n

readℤ₁₀ : String → Maybe ℤ
readℤ₁₀ str = do
  (u , v) ← String.uncons str
  if u Char.== '-'
    then (do
      n ← readℕ₁₀ v
      return (ℤ.- (+ n)))
    else (do
      n ← readℕ₁₀ str
      return (+ n))

readDouble : String → Maybe (ℤ × ℕ × ℕ)
readDouble str = do
  let characters = String.toList str
  let (integerChars , fractionChars) = breakᵇ (Char._== '.') characters
  integer ← readℤ₁₀ (String.fromList integerChars)
  fraction ← readℕ₁₀ (String.fromList fractionChars)
  return (integer , fraction , length fractionChars)
  
readRational : String → Maybe ℝ
readRational num = do
  (integer , fraction , fractionLength) ← readDouble num
  let denominator = 10 ℕ.^ fractionLength
  let numerator = integer ℤ.* (+ denominator) ℤ.+ (+ fraction)
  return (ℚ._/_ numerator denominator {{^-nonZero 10 fractionLength}})

readFloat64 : String → Maybe Float
readFloat64 str = do
  q ← readRational str
  let numerator = Float.fromℤ (↥ q)
  let denominator = Float.fromℕ (↧ₙ q)
  return (numerator Float.÷ denominator) 
