module Data.Functor.Container where

open import Basics
open import Data.EndoFunctor

record Con : Set₁ where
  constructor _◃_
  field
    Sh : Set
    Po : Sh → Set
  ⟦_⟧◃  : Set → Set
  ⟦_⟧◃ X = Σ Sh λ s → Po s → X
open Con public
infixr 1 _◃_

K◃ : Set → Con
K◃ A = A ◃ λ _ → Zero

I◃ : Con
I◃ = One ◃ λ _ → One

_+◃_ : Con → Con → Con
(S ◃ P) +◃ (S₁ ◃ P₁) = (S ⊎ S₁) ◃ vv P ⟨?⟩ P₁

_×◃_ : Con → Con → Con
(S ◃ P) ×◃ (S₁ ◃ P₁) = (S × S₁) ◃ vv λ s s₁ → P s ⊎ P₁ s₁ 

Σ◃ : (A : Set)(C : A → Con) → Con
Σ◃ A C = (Σ A λ a → Sh (C a)) ◃ vv λ a s → Po (C a) s

Π◃ : (A : Set)(C : A → Con) → Con
Π◃ A C = ((a : A) → Sh (C a)) ◃ (λ f → Σ A λ a → Po (C a) (f a))

_∘◃_ : Con → Con → Con
(S ◃ P) ∘◃ C = Σ◃ S λ s → Π◃ (P s) λ p → C

conEndoFunctor : {C : Con} → EndoFunctor ⟦ C ⟧◃
conEndoFunctor {S ◃ P} = record { map = λ f x → (fst x) , (λ z → f (snd x z)) }

conEndoFunctorOKP : {C : Con} → EndoFunctorOKP ⟦ C ⟧◃ {{conEndoFunctor}}
conEndoFunctorOKP {S ◃ P} = record
  { endoFunctorId = λ x → refl
  ; endoFunctorCo = λ f g x → refl
  }

_⟶◃_ : Con → Con → Set
(S ◃ P) ⟶◃ (S₁ ◃ P₁) = Σ (S → S₁) λ f → (s : S) → P₁ (f s) → P s

_/◃_ : ∀ {C C₁} → C ⟶◃ C₁ → ∀ {X} → ⟦ C ⟧◃ X → ⟦ C₁ ⟧◃ X
(to , fro) /◃ (s , k) = to s , k ∘ fro s 

morph◃ : ∀ {C C₁} → (∀ {X} → ⟦ C ⟧◃ X → ⟦ C₁ ⟧◃ X) → C ⟶◃ C₁
morph◃ f = (λ x → fst (f (x , id))) , (λ s → snd (f (s , id)))

id⟶◃ : ∀ {C} → C ⟶◃ C
id⟶◃ = id , (λ _ x → x)

_∘⟶◃_ : ∀ {C D E} → (D ⟶◃ E) → (C ⟶◃ D) → (C ⟶◃ E)
(toe , froe) ∘⟶◃ (tod , frod) = toe ∘ tod , (λ s z → frod s (froe (tod s) z))


