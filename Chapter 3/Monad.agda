module Monad where
  open import Basics
--  open import Vector
  open import Applicative

  record Monad (F : Set → Set) : Set₁ where
    field
      return : ∀ { X } → X → F X
      _>>=_ : ∀ { S T } → F S → (S → F T) → F T
    monadApplicative : Applicative F
    monadApplicative = record
      { pure = return
      ; _⍟_ =  λ ff fs → ff >>= λ f → fs >>= λ s → return (f s)
      }
  open Monad {{...}} public

{-
  monadVec : { n : ℕ } → Monad λ X → Vec X n
  monadVec = record
    { return = vec
    ; _>>=_ = {! !}
    }
-}
