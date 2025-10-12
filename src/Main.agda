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

open import vnnlib-semantics
open import vnnlib-types
open import vnnlib-syntax using (Query)

-- This only prints if there is an error or if the semantics has been computed
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
  Err.ok result ← parseQuery <$> readFiniteFile file where
    Err.bad msg → do
      putStrLn "PARSE FAILED\n"
      putStrLn (stringFromList msg)
      exitFailure
  printQuery (check result)
