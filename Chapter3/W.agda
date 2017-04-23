module Chapter3.W where

open import Meta.Basics
open import Chapter3.Containers
open import Meta.Control.Monad

-- The least fixed point of a container is a Well-Founded Type.
data W (C : Con) : Set where
  ⟨_⟩ : ⟦ C ⟧◃ (W C) → W C

-- The well-founded type of natural numbers is the type with Two constructors
-- given by Zero (⊥) or One (⊤)
NatW : Set
NatW = W (Two ◃ Zero ⟨?⟩ One)

-- Now for the constructors:

-- zero selects the Zero constructor that has a... er... "magic" shape.  Such is
-- life.
zeroW : NatW
zeroW = ⟨ tt , magic ⟩

-- suc(n) has a shape that selects the underlying n.
sucW : NatW → NatW
sucW n = ⟨ tt , (λ _ → n) ⟩

-- Primitive recursion over well-founded nats.
precW : ∀ {l}{T : Set l} → T → (NatW → T → T) → NatW → T
precW z _ ⟨ tt , _ ⟩ = z
precW z s ⟨ ff , k ⟩ = s (k <>) (precW z s (k <>))

-- Addition is then defined using primitive recursion by standard application of
-- the suc constructor.
addW : NatW → NatW → NatW
addW x y = precW y (λ _ → sucW) x

--
_*◃_ : Con → Set → Set
C *◃ X = W (K◃ X +◃ C)

-- The free monad for a Container.
freeMonad : (C : Con) → Monad (_*◃_ C)
freeMonad C = record
  { return = λ x → ⟨ (tt , x) , magic ⟩ -- Like zeroW but carries an element
  ; _>>=_ = bind
  } where
    bind : ∀ {S T : Set} → C *◃ S → (S → C *◃ T) → C *◃ T
    bind ⟨ (tt , a) , _ ⟩ f = f a
    bind ⟨ (ff , s) , k ⟩ f = ⟨ (ff , s) , (λ x → bind (k x) f) ⟩

-- Free monad closure. Respects C * X ≅ ⟦ C*◃ ⟧◃ X
_*◃ : Con → Con
_*◃ C = C *◃ One ◃ Path where
  Path : C *◃ One → Set
  Path ⟨ (tt , _) , _ ⟩ = One
  Path ⟨ (ff , s) , k ⟩ = Σ (Po C s) λ p → Path (k p)

-- Performs one command-response interaction.  Look, it `bind`.
call : ∀ {C} → (s : Sh C) → C *◃ Po C s
call s = ⟨ (ff , s) , (λ x → ⟨ (tt , x) , magic ⟩) ⟩

-- "We can model the general recursive function space as the means to perform
-- finite, on demand expansion of call trees."
Π⊥ : (S : Set) (T : S → Set) → Set
Π⊥ S T = (s : S) → (S ◃ T) *◃ (T s)

-- Give the 'gasoline-drive' interpreter for this function space, delivering
-- a result provided the call tree does not expand more times than a given
-- number.
gas : ∀ {S T} → ℕ → Π⊥ S T → (s : S) → T s ⊎ One
gas zero f s = ff , <>
gas {S}{T} (suc n) f s = combust (f s) where
  combust : ∀ {X} → (S ◃ T) *◃ X → X ⊎ One
  combust ⟨ (tt , s) , l ⟩ = tt , s
  combust ⟨ (ff , s) , l ⟩ with gas n f s
  combust ⟨ (ff , _) , l ⟩ | tt , t = combust (l t)
  combust ⟨ (ff , _) , l ⟩ | ff , _ = ff , <>

-- "We have
--    ⟦ S ◃ P ⟧◃ X = Σ S λ s → P s → X
-- but we could translate the right-hand side into a more mathematical notation
-- and observe that a container is something a bit like a power series
--    ⟦ S ◃ P ⟧◃ X = Σ_(s : S) X^(P s)
-- We might imagine computing a formal derivative of such a series, 'multiplying
-- down each index, then subtracting one', but we are not merely counting data
-- - they have individual existences.  Let us define a kind of 'dependent
-- decrement' subtracting a *particular* element from a type.
--
-- That is, an element of X ─ x is some element for X which is known to be
-- other than x."
_─_ : (X : Set) (x : X) → Set
X ─ x = Σ X λ x₁ → x₁ ≃ x → Zero

-- The formal derivative of a container.
--
-- The shape of a derivative is the pair of a shape with one position, which
-- we call the 'hole', and the positions in the derivative are 'everywhere but
-- the hole.'
∂ : Con → Con
∂ (S ◃ P) = Σ S P ◃ vv λ s p → P s ─ p

-- A container morphism that witnesses the ability to fill the hole, provided
-- equality on positions is decidable.
plug : ∀ {C} → ((s : Sh C)(p p₁ : Po C s) → Dec (p ≃ p₁)) → (∂ C ×◃ I◃) ⟶◃ C
plug {C} poeq? = (fst ∘ fst) , (λ { ((s , x) , _) x₁ → nplay s x x₁ }) where
  nplay : (s : Sh C)(x x₁ : Po C s) → (Po C s ─ x) ⊎ One
  nplay s x x₁ with poeq? s x₁ x
  nplay s x .x | tt , refl = ff , <>
  nplay s x x₁ | ff , pp = tt , x₁ , pp
