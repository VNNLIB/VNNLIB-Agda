module Data.Real where

open import Data.Rational public
  using
  ( _≤ᵇ_
  ; _-_
  ; _+_
  ; _*_
  )
  renaming
  ( ℚ to ℝ
  ; 0ℚ to 0ℝ
  ; 1ℚ to 1ℝ
  )

open import Data.RationalUtils public
