module Meta.Basics where

open import Agda.Primitive using (Level)

id : ∀ {k}{X : Set k} → X → X
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

_∘_ : ∀ {i j k}
        {A : Set i}{B : A → Set j}{C : (a : A) → B a → Set k} →
        (f : {a : A}(b : B a) → C a b) →
        (g : (a : A) → B a) →
        (a : A) → C a (g a)
f ∘ g = λ a → f (g a)

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

infixr 9 _∘_

_$′_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $′ x = f x

infixr -20 _$′_

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

infixl 0 _∋_

data ℕ : Set where
  zero  :     ℕ
  suc   : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)
infixr 6 _+_

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y
infixr 7 _*_

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc n = (x ^ n) * x

record Σ {l : Level}(S : Set l)(T : S → Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

_×_ : {l : Level} → Set l → Set l → Set l
_×_ S T = Σ S λ _ → T
infixr 4 _,_

-- The induction principle for Σ types.
vv_ : ∀ {k l}{S : Set k}{T : S → Set k}{P : Σ S T → Set l} →
      ((s : S)(t : T s) → P (s , t)) → -- Given a witness to the construction of P
      (p : Σ S T) → P p -- And a Σ, you get a p.
(vv p) (s , t) = p s t
infixr 1 vv_

record One {l : Level} : Set l where
  constructor <>
open One public

data _≃_ {l}{X : Set l}(x : X) : X → Set l where
  refl : x ≃ x
infix 1 _≃_
{-# BUILTIN EQUALITY _≃_ #-}

subst : ∀ {k l}{X : Set k}{s t : X} → s ≃ t → (P : X → Set l) → P s → P t
subst refl P p = p

_≐_ : ∀ {l}{S : Set l}{T : S → Set l} → (f g : (x : S) → T x) → Set l
f ≐ g = ∀ x → f x ≃ g x
infix 1 _≐_

begin_ : ∀ {l}{A : Set l}{x y : A} → x ≃ y → x ≃ y
begin_ p = p

_=[_⟩_ : ∀ {l}{X : Set l}(x : X){y z} → x ≃ y → y ≃ z → x ≃ z
_ =[ refl ⟩ q = q

_⟨_]=_ : ∀ {l}{X : Set l}(x : X){y z} → y ≃ x → y ≃ z → x ≃ z
_ ⟨ refl ]= q = q

_∎ : ∀ {l}{X : Set l}(x : X) → x ≃ x
x ∎ = refl

infix  3 _∎
infixr 2 _=[_⟩_ _⟨_]=_
infix  1 begin_

cong : ∀ {k l}{X : Set k}{Y : Set l}(f : X → Y){x y} → x ≃ y → f x ≃ f y
cong f refl = refl

sym : {X : Set} {s t : X} → s ≃ t → t ≃ s
sym refl = refl

trans : {X : Set} {r s t : X} → r ≃ s → s ≃ t → r ≃ t
trans refl refl = refl

data Two : Set where
  tt ff : Two

_⟨?⟩_ : ∀ {l}{P : Two → Set l} → P tt → P ff → (b : Two) → P b
(t ⟨?⟩ f) tt = t
(t ⟨?⟩ f) ff = f

_⊎_ : Set → Set → Set
S ⊎ T = Σ Two (S ⟨?⟩ T)

data Zero : Set where

-- ex falso.
magic : ∀ {l}{A : Set l} → Zero → A
magic ()

Dec : Set → Set
Dec X = X ⊎ (X → Zero)

data List (X : Set) : Set where
  ⟨⟩ : List X
  _,_ : X → List X → List X

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  ⟨⟩   #-}
{-# BUILTIN CONS _,_  #-}

length : {X : Set} → List X → ℕ
length ⟨⟩        = zero
length (x , xs)  = suc (length xs)

zip : {S T : Set} → List S → List T → List (S × T)
zip ⟨⟩ ⟨⟩ = ⟨⟩
zip (x , xs) (y , ys) = (x , y) , zip xs ys
zip _ _ = ⟨⟩


data _⁻¹_ { S T : Set }(f : S → T) : T → Set where
  from : (s : S) → f ⁻¹ f s


+-assoc  : ∀ a b c → a + (b + c) ≃ (a + b) + c -- hint: use cong
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)
{-
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)
-}
