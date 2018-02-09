module Chapter3.Containers where

open import Meta.Basics
open import Meta.Data.EndoFunctor

-- "Containers are the infinitary generalization of normal functors" by
record Con : Set₁ where
  constructor _◃_
  field
    Sh : Set -- a set of shapes
    Po : Sh → Set -- And a function taking shapes to "positions"
  ⟦_⟧◃  : Set → Set -- Containers can be interpreted in the dependent reader monad.
  ⟦_⟧◃ X = Σ Sh λ s → Po s → X
open Con public
infixr 1 _◃_

-- Conor says: "We may readily check that the polynomials are all containers."

-- Types are containers with a unique shape.
-- K◃ : X → (_ → 0)
K◃ : Set → Con
K◃ A = A ◃ λ _ → Zero

-- The identity container
-- I◃ : 1 → (_ → 1)
I◃ : Con
I◃ = One ◃ λ _ → One

-- The sum of containers is a container of sums
-- (X , XS) +◃ (Y : YS) = (X + Y) → (choose (XS + YS))
_+◃_ : Con → Con → Con
(S ◃ P) +◃ (S₁ ◃ P₁) = (S ⊎ S₁) ◃ vv P ⟨?⟩ P₁

-- The product of containers is a container of products
-- (X , XS) ×◃ (Y : YS) = (X × Y) → (selector → (XS + YS))
_×◃_ : Con → Con → Con
(S ◃ P) ×◃ (S₁ ◃ P₁) = (S × S₁) ◃ vv λ s s₁ → P s ⊎ P₁ s₁

-- Containers are closed under dependent pairs.
Σ◃ : (A : Set)(C : A → Con) → Con
Σ◃ A C = (Σ A λ a → Sh (C a)) ◃ vv λ a s → Po (C a) s

-- Containers are closed under dependent functions.
Π◃ : (A : Set)(C : A → Con) → Con
Π◃ A C = ((a : A) → Sh (C a)) ◃ (λ f → Σ A λ a → Po (C a) (f a))

-- Because of that, containers are closed under composition.
_∘◃_ : Con → Con → Con
(S ◃ P) ∘◃ C = Σ◃ S λ s → Π◃ (P s) λ p → C

conEndoFunctor : {C : Con} → EndoFunctor ⟦ C ⟧◃
conEndoFunctor {S ◃ P} = record
  { map = λ f x → (fst x) , (λ z → f (snd x z)) }

conEndoFunctorOKP : {C : Con} → EndoFunctorOKP ⟦ C ⟧◃ {{conEndoFunctor}}
conEndoFunctorOKP {S ◃ P} = record
  { endoFunctorId = λ x → refl
  ; endoFunctorCo = λ f g x → refl
  }

-- Also, containers model a natural transformation between the functors in the
-- each container by hooking up the input shapes of one container to the output
-- of the other then by hooking up the output positions to the input positions
-- form which to fetch elements.
_⟶◃_ : Con → Con → Set
(S ◃ P) ⟶◃ (S₁ ◃ P₁) = Σ (S → S₁) λ f → (s : S) → P₁ (f s) → P s

-- Action of the natural transformation.
_/◃_ : ∀ {C C₁} → C ⟶◃ C₁ → ∀ {X} → ⟦ C ⟧◃ X → ⟦ C₁ ⟧◃ X
(to , fro) /◃ (s , k) = to s , k ∘ fro s

-- Check that you can represent any natural transformation between containers as
-- a container morphism

morph◃ : ∀ {C C₁} → (∀ {X} → ⟦ C ⟧◃ X → ⟦ C₁ ⟧◃ X) → C ⟶◃ C₁
morph◃ f = (λ x → fst (f (x , id))) , (λ s → snd (f (s , id)))

-- The identity natural transformation for containers takes shapes back to
-- shapes and output positions to input positions.
id⟶◃ : ∀ {C} → C ⟶◃ C
id⟶◃ = id , (λ _ x → x)

-- Composition of container natural transformations.
_∘⟶◃_ : ∀ {C D E} → (D ⟶◃ E) → (C ⟶◃ D) → (C ⟶◃ E)
(toe , froe) ∘⟶◃ (tod , frod) = toe ∘ tod , (λ s z → frod s (froe (tod s) z))
