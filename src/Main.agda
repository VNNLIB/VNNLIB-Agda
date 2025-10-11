module Main where
open import Syntax.IOLib
open import Syntax.Parser using (Err; parseQuery)

open import Reflection.AST.Show using (showTerm)
open import vnnlib-check using (check)
open import Level using (0ℓ)
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import Reflection.AST
open import Agda.Builtin.Reflection
open import Data.Nat
open import Data.Bool

open import vnnlib-semantics
open import vnnlib-syntax
open import vnnlib-normaliseQuery using (normaliseQuery)

query = mkQuery [] ( assert (literal true) ∷ [])

small_vcl : String
small_vcl = " (vnnlib-version <2.0>)

(assert (
    and (>= 2.1 0) (and (!= 0 1) (> 9 8))))
"

parsed : Err _
parsed = parseQuery small_vcl

Test = {!1 + 2!}


printQuery : Result Query → IO ⊤
printQuery (error err) = do
  putStrLn "ERROR:\n"
  putStrLn err
  exitFailure
printQuery (success q) = do
  let query = ⟦ q ⟧𝕢
  let normQuery = normalise (quoteTerm query)
  putStrLn (showTerm (quoteTerm query))


main : IO ⊤
main = do
  file ∷ [] ← getArgs where
    _ → do
      putStrLn "usage: Main <SourceFile>"
      exitFailure
  Err.ok result ← parseQuery <$> readFiniteFile "../VNNLIB-standard/test/acc.vnnlib" where
    Err.bad msg → do
      putStrLn "PARSE FAILED\n"
      putStrLn (stringFromList msg)
      exitFailure
  printQuery (check result)
