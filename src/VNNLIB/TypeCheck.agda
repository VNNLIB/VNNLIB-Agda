module VNNLIB.TypeCheck where

open import Data.String as String using (String)
open import Data.List as List
open import Data.List.NonEmpty as List⁺
open import VNNLIB.Syntax.AST as 𝐁 hiding (String)

open import VNNLIB.Syntax as 𝐕
open import VNNLIB.SyntaxUtils
open import Data.RationalUtils
open import Data.FloatUtils
open import VNNLIB.TypeCheck.Declarations
open import VNNLIB.TypeCheck.Assertions

open import Level
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Effect.Monad

open RawMonad monad

checkAssertions : (Σ : List 𝐕.NetworkDefinition) → List 𝐁.Assertion → Result (List (𝐕.Assertion (mkContext Σ)))
checkAssertions Σ asserts = List.foldl checkAsserts (success []) asserts
  where
    checkAssert : 𝐁.Assertion → Result (𝐕.Assertion (mkContext Σ))
    checkAssert (assert b) = do
      b' ← checkBoolExpr Σ b
      return (assert b')

    checkAsserts : Result (List (𝐕.Assertion (mkContext Σ))) → 𝐁.Assertion → Result (List (𝐕.Assertion (mkContext Σ)))
    checkAsserts (error e) _ = error e
    checkAsserts (success asserts) a = do
      a' ← checkAssert a
      return (a' ∷ asserts)
    
-- Check a VNN-LIB query
checkQuery : List 𝐁.NetworkDefinition → List 𝐁.Assertion → Result 𝐕.Query
checkQuery defs asserts = do
  defs' ← mkCheckContext defs
  asserts' ← checkAssertions defs' asserts
  return (𝐕.mkQuery defs' asserts')

-- Parser Entrypoint
check : 𝐁.Query → Result 𝐕.Query
check (vNNLibQuery ver ns as) = do
  assertions ← (convertListToList⁺ as) -- cannot have non-empty list of assertions
  query ← checkQuery ns (toList assertions)
  return query
