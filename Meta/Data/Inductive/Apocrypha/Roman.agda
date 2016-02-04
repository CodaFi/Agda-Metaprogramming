module Meta.Data.Inductive.Apocrypha.Roman where

open import Meta.Basics
open import Meta.Data.Functor.Container.Indexed
open import Meta.Data.Inductive.ITree
open import Meta.Data.Functor.Container
open import Meta.Data.Inductive.W

record Roman (I J : Set) : Set₁ where
  constructor SPqr
  field
    S : Set
    P : S → Set
    q : S → J
    r : (s : S) → P s → I
  Plain : Con
  Plain = S ◃ P
  ⟦_⟧R : (I → Set) → (J → Set)
  ⟦_⟧R X j = Σ (Σ S λ s → q s ≃ j) (vv λ s _ → (p : P s) → X (r s p))
  
Plain = Roman.Plain
⟦_⟧R = Roman.⟦_⟧R


FromRoman : ∀ {I J} → Roman I J → I ▷ J
FromRoman (SPqr S P q r) = (λ j → Σ S λ s → q s ≃ j)
                         ◃ (λ j → P ∘ fst)
                         $ (λ f → r ∘ fst)

onTheNose : ∀ {I J} (C : Roman I J) → ⟦ C ⟧R ≃ ⟦ FromRoman C ⟧ᵢ
onTheNose C = refl

ToRoman : ∀ {I J} → I ▷ J → Roman I J
ToRoman {I}{J} (Shlx ◃ Polx $ rilx) = SPqr (Σ J Shlx) (vv Polx) fst (vv rilx)

toRoman : ∀ {I J} (C : I ▷ J) →
          ∀ {X j} → ⟦ C ⟧ᵢ X j → ⟦ ToRoman C ⟧R X j
toRoman C (fst , snd) = ((_ , fst) , refl) , snd

fromRoman : ∀ {I J} (C : I ▷ J) →
            ∀ {X j} → ⟦ ToRoman C ⟧R X j → ⟦ C ⟧ᵢ X j
fromRoman C (((j , snd) , refl) , snd₂) = snd , snd₂

toAndFromRoman : ∀ {I J} (C : I ▷ J){X j}
                 → (∀ xs → toRoman C {X}{j} (fromRoman C {X}{j} xs) ≃ xs)
                 × (∀ xs → fromRoman C {X}{j} (toRoman C {X}{j} xs) ≃ xs)
toAndFromRoman C = (λ { (((_ , _) , refl) , _) → refl }) , (λ xs → refl)

data RomanData {I} (C : Roman I I) : I → Set where
  _,_ : (s : Roman.S C) → ((p : Roman.P C s) → RomanData C (Roman.r C s p)) → RomanData C (Roman.q C s)

ideology : ∀ {I} (C : Roman I I) → I → W (Plain C) → W (Plain C ×◃ K◃ I)
ideology C i ⟨ s , k ⟩ = ⟨ ((s , i) , (λ { (tt , p) → ideology C (Roman.r C s p) (k p) ; (ff , ()) })) ⟩

phenomenology : ∀ {I} (C : Roman I I) → W (Plain C) → W (Plain C ×◃ K◃ I)
phenomenology C ⟨ s , k ⟩ = ⟨ ((s , Roman.q C s) , (λ { (tt , snd) → phenomenology C (k snd) ; (ff , ()) })) ⟩

RomanW : ∀ {I} → Roman I I → I → Set
RomanW C i = Σ (W (Plain C)) λ t → phenomenology C t ≃ ideology C i t

fromRomanW : ∀ {I} (C : Roman I I) {i} → RomanW C i → RomanData C i
fromRomanW C (t , good) = {!!}

postulate
  extensionality : ∀ {S : Set}{T : S → Set} (f g : (s : S) → T s) → ((s : S) → f s ≃ g s) → f ≃ g

toRomanW : ∀ {I} (C : Roman I I) {i} → RomanData C i → RomanW C i
toRomanW C t = {!!}

data _** {I : Set} (R : I × I → Set) : I × I → Set where
  ⟨⟩  : {i : I}     → (R **) (i , i)
  _,_ : {i j k : I} → R (i , j) → (R **) (j , k) → (R **) (i , k)
infix 1 _**

NAT : Set
NAT = (Loop **) _ where
  Loop : One × One → Set
  Loop _ = One

one : ∀ {I}{R : I × I → Set} → R -:> (R **)
one (fst , snd) x = x , ⟨⟩

join** : ∀ {I}{R : I × I → Set} → ((R **) **) -:> (R **)
join** (_ , _) ⟨⟩ = ⟨⟩
join** (i , snd) (x , xs) = {!!}

Pow : Set₁ → Set₁
Pow X = X → Set

Fam : Set₁ → Set₁
Fam X = Σ Set λ I → I → X

p2f : (Pow ∘ ⇑) -:> (Fam ∘ ⇑)
p2f X P = (Σ X (P ∘ ↑)) , (↑ ∘ fst)

f2p : (Fam ∘ ⇑) -:> (Pow ∘ ⇑)
f2p X (I , f) (↑ x) = Σ I λ i → ↓ (f i) ≃ x

_$p_ : ∀ {I J} → (J → I) → Pow I → Pow J
f $p P = P ∘ f

_$F_ : ∀ {I J} → (I → J) → Fam I → Fam J
f $F (F , i) = F , (f ∘ i)

ROMAN : Set → Set → Set1
ROMAN I J = Σ (Fam (⇑ J)) λ { (S , q) → S → Fam (⇑ I) }

HANCOCK : Set → Set → Set1
HANCOCK I J = Σ (Pow (⇑ J)) λ S → Σ J (S ∘ ↑) → Fam (⇑ I)

NOTTINGHAM : Set → Set → Set₁
NOTTINGHAM I J = Σ (Pow (⇑ J)) λ S → Σ J (S ∘ ↑) → Pow (⇑ I)

HANCOCK' : Set → Set → Set₁
HANCOCK' I J = J → Fam (Fam (⇑ I))

NOTTINGHAM' : Set → Set → Set₁
NOTTINGHAM' I J = J → Fam (Pow (⇑ I))


