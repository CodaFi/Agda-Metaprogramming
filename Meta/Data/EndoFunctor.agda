module Meta.Data.EndoFunctor where

open import Meta.Basics

record EndoFunctor (F : Set → Set) : Set₁ where
  constructor MkEndo
  field
    map : ∀ { S T } → (S → T) → F S → F T
open EndoFunctor {{...}} public

{-
record EndoFunctorOK F {{FF : EndoFunctor F}} : Set₁ where
  field
    endoFunctorId : ∀ {X} → map {{FF}}{X} id ≃ id
    endoFunctorCo : ∀ {R S T} → (f : S → T)(g : R → S) → map {{FF}} f ∘ map g ≃ map (f ∘ g)
open EndoFunctorOK {{...}} public
-}

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set₁ where
  field
    endoFunctorId : ∀ {X} → map {{FF}}{X} id ≐ id
    endoFunctorCo : ∀ {R S T} → (f : S → T)(g : R → S) → map {{FF}} f ∘ map g ≐ map (f ∘ g)
open EndoFunctorOKP {{...}} public
