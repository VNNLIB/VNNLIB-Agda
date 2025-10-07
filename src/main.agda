module main where
open import Syntax.IOLib
open import Syntax.Parser using (Err; parseQuery)

open import vnnlib-check using (check)
open import vnnlib-printQuery using (printQuery)

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
