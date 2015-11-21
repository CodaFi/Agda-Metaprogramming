module Basics where

open import Level using (Level) renaming (zero to lzero; suc to lsuc)

_∘_ : forall {i j k}
        {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b) ->
        (g : (a : A) -> B a) ->
        (a : A) -> C a (g a)
f ∘ g = λ a → f (g a)

id : forall {k}{X : Set k} -> X -> X
id x = x

data ℕ : Set where
  zero  :      ℕ
  suc   : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)
infixr 5 _+_

_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = x * y + y
infixr 6 _*_

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc n = (x ^ n) * x

record Σ {l : Level}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

_×_ : {l : Level} -> Set l -> Set l -> Set l
_×_ S T = Σ S \ _ -> T
infixr 4 _,_

vv_ : ∀ {k l}{S : Set k}{T : S -> Set k}{P : Σ S T -> Set l} →
      ((s : S)(t : T s) → P (s , t)) →
      (p : Σ S T) → P p
(vv p) (s , t) = p s t
infixr 1 vv_

record One {l : Level} : Set l where
  constructor <>
open One public

data _≃_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x ≃ x
infix 1 _≃_
{-# BUILTIN EQUALITY _≃_ #-}
{-# BUILTIN REFL refl #-}

subst : ∀ {k l}{X : Set k}{s t : X} → s ≃ t -> (P : X → Set l) → P s → P t
subst refl P p = p

_≐_ : ∀ {l}{S : Set l}{T : S → Set l} → (f g : (x : S) → T x) → Set l
f ≐ g = ∀ x → f x ≃ g x
infix 1 _≐_

_=[_⟩_ : forall {l}{X : Set l}(x : X){y z} → x ≃ y → y ≃ z → x ≃ z
_ =[ refl ⟩ q = q

_⟨_]=_ : forall {l}{X : Set l}(x : X){y z} → y ≃ x → y ≃ z → x ≃ z
_ ⟨ refl ]= q = q

_∎ : forall {l}{X : Set l}(x : X) → x ≃ x
x ∎ = refl

infixr 1 _=[_⟩_ _⟨_]=_ _∎

cong : forall {k l}{X : Set k}{Y : Set l}(f : X -> Y){x y} → x ≃ y → f x ≃ f y
cong f refl = refl

symmetry :  {X : Set} {s t : X} -> s ≃ t -> t ≃ s
symmetry refl = refl

data Two : Set where
  tt ff : Two
  
_⟨?⟩_ : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
(t ⟨?⟩ f) tt = t
(t ⟨?⟩ f) ff = f

_⊎_ : Set -> Set -> Set
S ⊎ T = Σ Two (S ⟨?⟩ T)

data Zero : Set where

magic : forall {l}{A : Set l} -> Zero -> A
magic ()

Dec : Set -> Set
Dec X = X ⊎ (X -> Zero)

data List (X : Set) : Set where
  ⟨⟩ : List X
  _,_ : X → List X → List X

length : {X : Set} -> List X -> ℕ
length ⟨⟩        = zero
length (x , xs)  = suc (length xs)

zip : {S T : Set} → List S → List T → List (S × T)
zip ⟨⟩ ⟨⟩ = ⟨⟩
zip (x , xs) (y , ys) = (x , y) , zip xs ys
zip _ _ = ⟨⟩

data _⁻¹_ { S T : Set }(f : S → T) : T → Set where
  from : (s : S) → f ⁻¹ f s
  
