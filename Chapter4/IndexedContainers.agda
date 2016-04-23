module Chapter4.IndexedContainers where

open import Agda.Primitive
open import Meta.Basics
open import Meta.Language.LambdaCalculus

-- An I ▷ J describes J sorts of structures in terms of I sorts of elements.
--
-- "Hancock calls these indexed containers 'interaction structures.' Consider
-- J to be the set of possible 'states of the world' before an interaction,
-- and I to be the possible states afterward.  The 'before' states will
-- determine a choice of commands we can issue, each of which has a set of
-- possible responses which will then determine the state 'after'.  An
-- interaction structures thus describes the predicate transformer which
-- describes the precondition for achieving a postcondition by one step of
-- interaction. We are just using proof-relevant Hoare logic as the type system!"
record _▷_ (I J : Set) : Set₁ where
  constructor _◃_$_
  field
    ShIx : J → Set -- A J-indexed thing
    PoIx : (j : J) → ShIx j → Set -- that determines places for
    riIx : (j : J) (s : ShIx j) (p : PoIx j s) → I -- I elements
  ⟦_⟧ᵢ : (I → Set) → (J → Set)
  ⟦_⟧ᵢ X j = Σ (ShIx j) λ s → (p : PoIx j s) → X (riIx j s p)
open _▷_ public

-- The interpretation of indexed containers as operations on indexed families of
-- sets.
_-:>_ : ∀ {k l}{I : Set k} → (I → Set l) → (I → Set l) → Set (l ⊔ k)
X -:> Y = ∀ i → X i → Y i

-- The functorial action for indexed containers as operations on indexed families
-- of sets.
ixMap : ∀ {I J}{C : I ▷ J}{X Y} → (X -:> Y) → ⟦ C ⟧ᵢ X -:> ⟦ C ⟧ᵢ Y
ixMap f j (s , k) = s , λ p → f _ (k p)
