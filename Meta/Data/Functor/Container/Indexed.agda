module Meta.Data.Functor.Container.Indexed where

open import Agda.Primitive
open import Meta.Basics
open import Meta.Language.LambdaCalculus

record _▷_ (I J : Set) : Set₁ where
  constructor _◃_$_
  field
    Shlx : J → Set
    Polx : (j : J) → Shlx j → Set
    rilx : (j : J) (s : Shlx j) (p : Polx j s) → I
  ⟦_⟧ᵢ : (I → Set) → (J → Set)
  ⟦_⟧ᵢ X j = Σ (Shlx j) λ s → (p : Polx j s) → X (rilx j s p)
open _▷_ public

_-:>_ : ∀ {k l}{I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
X -:> Y = ∀ i → X i → Y i

ixMap : ∀ {I J}{C : I ▷ J}{X Y} → (X -:> Y) → ⟦ C ⟧ᵢ X -:> ⟦ C ⟧ᵢ Y
ixMap f j (s , k) = s , λ p → f _ (k p)
