module main where
open import Syntax.IOLib
open import Syntax.AST using (printQuery)
open import Syntax.Parser using (Err; parseQuery)

open import Data.String using (String; _++_)
open import Level using (0ℓ)
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)
open import vnnlib-check
open import Agda.Builtin.Unit using (⊤ ; tt)
open import vnnlib-syntax as 𝐒
open import vnnlib-semantics

printSQuery : Query → String
printSQuery q = let 𝕢 = ⟦ q ⟧𝕢 in {!!}

parseSQuery : Result Query → String
parseSQuery (error x) = "ERROR\n" ++ x
parseSQuery (success y) = printSQuery y

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
  let parsedQuery = parseSQuery (check result)
  putStrLn (parsedQuery)
