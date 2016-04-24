module Meta.Data.Inductive.W where

open import Meta.Basics
open import Meta.Data.Functor.Container
open import Meta.Control.Monad

data W (C : Con) : Set where
  ⟨_⟩ : ⟦ C ⟧◃ (W C) → W C

NatW : Set
NatW = W (Two ◃ Zero ⟨?⟩ One)

zeroW : NatW
zeroW = ⟨ tt , magic ⟩

sucW : NatW → NatW
sucW n = ⟨ tt , (λ _ → n) ⟩

precW : ∀ {l}{T : Set l} → T → (NatW → T → T) → NatW → T
precW z _ ⟨ tt , _ ⟩ = z
precW z s ⟨ ff , k ⟩ = s (k <>) (precW z s (k <>))

addW : NatW → NatW → NatW
addW x y = precW y (λ _ → sucW) x

_*◃_ : Con → Set → Set
C *◃ X = W (K◃ X +◃ C)

freeMonad : (C : Con) → Monad (_*◃_ C)
freeMonad C = record
  { return = λ x → ⟨ (tt , x) , magic ⟩
  ; _>>=_ = bind
  } where
    bind : ∀ {S T : Set} → C *◃ S → (S → C *◃ T) → C *◃ T
    bind ⟨ (tt , a) , _ ⟩ f = f a
    bind ⟨ (ff , s) , k ⟩ f = ⟨ (ff , s) , (λ x → bind (k x) f) ⟩

_*◃ : Con → Con
_*◃ C = C *◃ One ◃ Path where
  Path : C *◃ One → Set
  Path ⟨ (tt , _) , _ ⟩ = One
  Path ⟨ (ff , s) , k ⟩ = Σ (Po C s) λ p → Path (k p)

call : ∀ {C} → (s : Sh C) → C *◃ Po C s
call s = ⟨ (ff , s) , (λ x → ⟨ (tt , x) , magic ⟩) ⟩

Π⊥ : (S : Set) (T : S → Set) → Set
Π⊥ S T = (s : S) → (S ◃ T) *◃ (T s)

gas : ∀ {S T} → ℕ → Π⊥ S T → (s : S) → T s ⊎ One
gas zero f s = ff , <>
gas {S}{T} (suc n) f s = combust (f s) where
  combust : ∀ {X} → (S ◃ T) *◃ X → X ⊎ One
  combust ⟨ (tt , s) , l ⟩ = tt , s
  combust ⟨ (ff , s) , l ⟩ with gas n f s
  combust ⟨ (ff , _) , l ⟩ | tt , t = combust (l t)
  combust ⟨ (ff , _) , l ⟩ | ff , _ = ff , <>

_─_ : (X : Set) (x : X) → Set
X ─ x = Σ X λ x₁ → x₁ ≃ x → Zero

δ : Con → Con
δ (S ◃ P) = Σ S P ◃ vv λ s p → P s ─ p

plug : ∀ {C} → ((s : Sh C)(p p₁ : Po C s) → Dec (p ≃ p₁)) → (δ C ×◃ I◃) ⟶◃ C
plug {C} poeq? = (fst ∘ fst) , (λ { ((s , x) , _) x₁ → nplay s x x₁ }) where
  nplay : (s : Sh C)(x x₁ : Po C s) → (Po C s ─ x) ⊎ One
  nplay s x x₁ with poeq? s x₁ x
  nplay s x .x | tt , refl = ff , <>
  nplay s x x₁ | ff , pp = tt , x₁ , pp
  
