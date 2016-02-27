module Chapter4.IndexedContainers where

open import Meta.Basics
open import Level renaming (suc to lsuc)
open import Meta.Language.LambdaCalculus

record _▷_ (I J : Set) : Set₁ where
  constructor _◃_$_
  field
    ShIx : J → Set
    PoIx : (j : J) → ShIx j → Set
    riIx : (j : J) (s : ShIx j) (p : PoIx j s) → I
  ⟦_⟧ᵢ : (I → Set) → (J → Set)
  ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
open _▷_ public

_-:>_ : ∀ {k l}{I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
X -:> Y = ∀ i → X i → Y i

ixMap : ∀ {I J}{C : I ▷ J}{X Y} → (X -:> Y) → ⟦ C ⟧ᵢ X -:> ⟦ C ⟧ᵢ Y
ixMap f j (s , k) = s , λ p → f _ (k p)
