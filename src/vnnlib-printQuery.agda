module vnnlib-printQuery where

open import Agda.Builtin.Reflection
open import Reflection.AST.Show using (showTerm)
open import Agda.Builtin.Unit using (⊤ ; tt)
open import Agda.Builtin.IO using (IO)
open import Data.String using (String)
open import Syntax.IOLib

open import Level using (0ℓ)
open import Data.Sum.Effectful.Left String 0ℓ renaming (Sumₗ to Result)
open import Data.Sum.Base renaming (inj₁ to error; inj₂ to success)

open import vnnlib-semantics
open import vnnlib-syntax

printQuery : Result Query → IO ⊤
printQuery (error err) = do
  putStrLn "ERROR:\n"
  putStrLn err
  exitFailure
printQuery (success q) = do
  let 𝕢 = ⟦ q ⟧𝕢 -- get the query function object
  putStrLn (showTerm (quoteTerm 𝕢))
