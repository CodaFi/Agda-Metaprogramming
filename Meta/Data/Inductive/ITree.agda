module Meta.Data.Inductive.ITree where

open import Agda.Primitive

open import Meta.Basics
open import Meta.Data.Functor.Container.Indexed
open import Meta.Language.LambdaCalculus

data ITree {J : Set} (C : J ▷ J)(j : J) : Set where
  ⟨_⟩ : ⟦ C ⟧ᵢ (ITree C) j → ITree C j

NatC : One ▷ One
NatC = (λ _ → Two) ◃ (λ _ → Zero ⟨?⟩ One) $ _

zeroC : ITree NatC <>
zeroC = ⟨ tt , magic ⟩

sucC : ITree NatC <> → ITree NatC <>
sucC n = ⟨ ff , (λ _ → n) ⟩

VecC : Set → ℕ ▷ ℕ
VecC X = VS ◃ VP $ Vr where
  VS : ℕ → Set
  VS zero = One
  VS (suc n) = X

  VP : (n : ℕ) → VS n → Set
  VP zero _ = Zero
  VP (suc n) _ = One

  Vr : (n : ℕ)(s : VS n)(p : VP n s) → ℕ
  Vr zero <> ()
  Vr (suc n) x <> = n

vnil' : ∀ {X} → ITree (VecC X) 0
vnil' = ⟨ <> , (λ ()) ⟩

vcons' : ∀ {X n} → X → ITree (VecC X) n → ITree (VecC X) (suc n)
vcons' x xs = ⟨ (x , (λ _ → xs)) ⟩

IsArr : ⋆ → Set
IsArr ι = Zero
IsArr (_ ▹ _) = One

STLC : (Cx ⋆ × ⋆) ▷ (Cx ⋆ × ⋆)
STLC = (vv λ Γ T → (T ∈ Γ) ⊎ (⋆ ⊎ IsArr T)) ◃ (λ { (Γ , τ) (tt , _) → Zero
                                                  ; (Γ , τ) (ff , (tt , l)) → Two
                                                  ; (Γ , τ) (ff , (ff , l)) → One
                                                  }) $
                                               (λ { (Γ , τ) (tt , _) ()
                                                  ; (Γ , τ) (ff , (tt , σ)) tt → Γ , (σ ▹ τ)
                                                  ; (Γ , τ) (ff , (tt , σ)) ff → Γ , σ
                                                  ; (Γ , ι) (ff , (ff , ())) _
                                                  ; (Γ , (σ ▹ τ)) (ff , (ff , p)) _ → (Γ , σ) , τ
                                                  })
Idlx : ∀ {I} → I ▷ I
Idlx = (λ _ → One) ◃ (λ j _ → One) $ (λ j _ _ → j)

Colx : ∀ {I J K} → J ▷ K → I ▷ J → I ▷ K
Colx (S ◃ P $ r) (S₁ ◃ P₁ $ r₁) = (λ x → Σ (S x) λ s → (p : P x s) → S₁ (r x s p))
                                ◃ (λ x → vv λ s f → Σ (P x s) λ p → P₁ (r x s p) (f p))
                                $ (λ { j (s , f) (p , p₁) → r₁ (r j s p) (f p) p₁ })

data Desc {l} (I : Set l) : Set (lsuc l) where
  var : I → Desc I
  σ π : (A : Set l) (D : A → Desc I) → Desc I
  _×D_ : Desc I → Desc I → Desc I
  κ : Set l → Desc I
infixr 4 _×D_

⟦_⟧D : ∀ {l}{I : Set l} → Desc I → (I → Set l) → Set l
⟦ (var i) ⟧D X = X i
⟦ (σ A D) ⟧D X = Σ A λ a → ⟦ D a ⟧D X
⟦ (π A D) ⟧D X = (a : A) → ⟦ D a ⟧D X
⟦ (D ×D E) ⟧D X = ⟦ D ⟧D X × ⟦ E ⟧D X
⟦ (κ A) ⟧D X = A

ixConDesc : ∀ {I J} → I ▷ J → J → Desc I
ixConDesc (S ◃ P $ r) j = σ (S j) λ s → π (P j s) λ p → var (r j s p)

DSh : {I : Set} → Desc I → Set
DSh (var x) = One
DSh (σ A D) = Σ A λ a → DSh (D a)
DSh (π A D) = (a : A) → DSh (D a)
DSh (D ×D D₁) = DSh D × DSh D₁
DSh (κ A) = A

DPo : ∀ {I} (D : Desc I) → DSh D → Set
DPo (var x) x₁ = One
DPo (σ A D) (x , y) = DPo (D x) y
DPo (π A D) f = Σ A λ a → DPo (D a) (f a)
DPo (D ×D D₁) (x , y) = DPo D x ⊎ DPo D₁ y
DPo (κ A) s = Zero

Dri : ∀ {I}(D : Desc I)(s : DSh D) → DPo D s → I
Dri (var x) s p = x
Dri (σ A D) (x , y) p = Dri (D x) y p
Dri (π A D) f (x , y) = Dri (D x) (f x) y
Dri (D ×D D₁) (x , y) (tt , p) = Dri D x p
Dri (D ×D D₁) (x , y) (ff , p) = Dri D₁ y p
Dri (κ x) s ()

descIxCon : ∀ {I J} → (J → Desc I) → I ▷ J
descIxCon F = (DSh ∘ F) ◃ (DPo ∘ F) $ (Dri ∘ F)

{-
vecD : Set → ℕ → Desc ℕ
vecD X n =
  σ Two ( κ (n ≃ 0)
        ⟨?⟩ σ ℕ λ k → κ X ×D var k ×D κ (n ≃ ℕ.suc k)
        )
-}

vecD : Set → ℕ → Desc ℕ
vecD X zero = κ One
vecD X (suc n) = κ X ×D var n

data Data {l}{J : Set l} (F : J → Desc J)(j : J) : Set l where
  ⟨_⟩ : ⟦ F j ⟧D (Data F) → Data F j

vnil : ∀ {X} → Data (vecD X) 0
vnil = ⟨ <> ⟩

vcons : ∀ {X n} → X → Data (vecD X) n → Data (vecD X) (suc n)
vcons x xs = ⟨ x , xs ⟩

record ⇑ {l}(X : Set l) : Set (lsuc l) where
  constructor ↑
  field
    ↓ : X
open ⇑ public

{-
data Desc⋆ {l} : Set l where
  varD σD πD ×D κD : Desc⋆

DescD : ∀ {l}(I : Set l) → One {lsuc l} → Desc (One {lsuc l})
DescD {l} I _ = Σ Desc⋆ (λ
  { varD → ? -- κD (⇑ I)
  ; σD → Σ (Set l) (λ A → π (⇑ A) λ _ → var <>)
  ; πD → Σ (Set l) (λ A → π (⇑ A) λ _ → var <>)
  ; ×D → ?
  ; κD → κD (Set l)
  })
-}

Everywhere : ∀ {I J} (C : I ▷ J)(X : I → Set) → Σ I X ▷ Σ J (⟦ C ⟧ᵢ X)
Everywhere (S ◃ P $ r) X
           = (λ _ → One)
           ◃ (λ {(j , (s , k)) _ → P j s })
           $ (λ { (j , (s , k)) _ p → r j s p , k p })

allTrivial : ∀ {I J} (C : I ▷ J)(X : I → Set) jc → ⟦ Everywhere C X ⟧ᵢ (λ _ → One) jc
allTrivial C X _ = <> , λ _ → <>

Somewhere : ∀ {I J}(C : I ▷ J)(X : I → Set) → Σ I X ▷ Σ J (⟦ C ⟧ᵢ X)
Somewhere (S ◃ P $ r) X
          = (λ { (j , (s , k)) → P j s})
          ◃ (λ { (j , (s , k)) _ → One})
          $ (λ { (j , (s , k)) p _ → r j s p , k p })

noMagic : ∀ {I J}(C : I ▷ J)(X : I → Set) jc → ⟦ Somewhere C X ⟧ᵢ (λ _ → Zero) jc → Zero
noMagic C X _ (p , m) = m <>

lookup : ∀ {I J}(C : I ▷ J)(X : I → Set) jc {Q R} → ⟦ Everywhere C X ⟧ᵢ Q jc → ⟦ Somewhere C X ⟧ᵢ R jc → ⟦ Somewhere C X ⟧ᵢ (λ ix → Q ix × R ix) jc
lookup C X jc (_ , q) (p , r) = p , (λ _ → (q p) , (r <>))

treeInd : ∀ {I}(C : I ▷ I)(P : Σ I (ITree C) → Set) →
  (⟦ Everywhere C (ITree C) ⟧ᵢ P -:>
  (vv λ i ts → P (i , ⟨ ts ⟩))) →
  (i : I)(t : ITree C i) → P (i , t)
treeInd C P m i ⟨ s , k ⟩ = m (i , (s , k)) (<> , λ p → treeInd C P m _ (k p))

treeFold : ∀ {I}(C : I ▷ I)(P : I → Set) →
             (⟦ C ⟧ᵢ P -:> P) →
             (ITree C -:> P)
treeFold C P m i ⟨ s , k ⟩ = m i (s , λ p → treeFold C P m _ (k p))

Children : ∀ {I} (C : I ▷ I) → Σ I (ITree C) ▷ Σ I (ITree C)
Children C = Colx (descIxCon (var ∘ buds)) (Everywhere C (ITree C))
  where
    buds : ∀ {I}{C : I ▷ I} → Σ I (ITree C) → Σ I λ i → ⟦ C ⟧ᵢ (ITree C) i
    buds (i , ⟨ xs ⟩) = i , xs

treeFoldInd : ∀ {I} (C : I ▷ I) P →
                    (⟦ Children C ⟧ᵢ P -:> P) →
                    ∀ it → P it
treeFoldInd C P m (i , t) = treeFold (Children C) P m (i , t) (children C i t)
  where
    children : ∀ {I}(C : I ▷ I) i t → ITree (Children C) (i , t)
    children C i ⟨ s , k ⟩ = ⟨ _ , (vv (λ _ p → children C _ (k p))) ⟩

EverywhereD SomewhereD : {I : Set}(D : Desc I)(X : I → Set) → ⟦ D ⟧D X → Desc (Σ I X)
EverywhereD (var x) X xs = var (x , xs)
EverywhereD (σ A D) X (x , xs) = EverywhereD (D x) X xs
EverywhereD (π A D) X f = π A λ a → EverywhereD (D a) X (f a)
EverywhereD (D ×D D₁) X (x , xs) = EverywhereD D X x ×D EverywhereD D₁ X xs
EverywhereD (κ x) X xs = κ One
SomewhereD (var x) X xs = var (x , xs)
SomewhereD (σ A D) X (x , xs) = SomewhereD (D x) X xs
SomewhereD (π A D) X f = σ A λ a → SomewhereD (D a) X (f a)
SomewhereD (D ×D D₁) X (x , xs) = σ Two (SomewhereD D X x ⟨?⟩ SomewhereD D₁ X xs)
SomewhereD (κ x) X xs = κ Zero

dataInd : ∀ {I : Set} (F : I → Desc I)(P : Σ I (Data F) → Set) →
                      ((i : I)(ds : ⟦ F i ⟧D (Data F)) →
                      ⟦ EverywhereD (F i) (Data F) ds ⟧D P → P (i , ⟨ ds ⟩)) →
                      ∀ i d → P (i , d)
dataInd F P m i ⟨ ds ⟩ = m i ds (lem (F i) ds) where
  lem : (D : Desc _)(ds : ⟦ D ⟧D (Data F)) → ⟦ EverywhereD D (Data F) ds ⟧D P
  lem (var x) d = dataInd F P m x d
  lem (σ A D) (l , r) = lem (D l) r
  lem (π A D) f a = lem (D a) (f a)
  lem (D ×D E) (l , r) = lem D l , lem E r
  lem (κ x) y = <>

vecNodeIx : (One ⊎ ℕ) ▷ ℕ
vecNodeIx = descIxCon {J = ℕ} λ
  { zero → κ One
  ; (suc n) → var (tt , <>) ×D var (ff , n)
  }

μlx : ∀ {I J} → (I ⊎ J) ▷ J → I ▷ J
μlx {I}{J} F = (ITree F₁ ∘ _,_ ff) ◃ (P₁ ∘ _,_ ff) $ (r₁ ∘ _,_ ff) where
  F₁ : (I ⊎ J) ▷ (I ⊎ J)
  F₁ = (vv (λ i → One) ⟨?⟩ Shlx F)
    ◃ (vv (λ _ _ → Zero) ⟨?⟩ Polx F)
    $ (vv (λ t s ()) ⟨?⟩ rilx F)
  P₁ : (x : I ⊎ J) → ITree F₁ x → Set
  P₁ (tt , i) _ = One
  P₁ (ff , j) ⟨ s , k ⟩ = Σ (Polx F j s) λ p → P₁ (rilx F j s p) (k p)

  r₁ : (x : I ⊎ J) (t : ITree F₁ x) → P₁ x t → I
  r₁ (tt , i) _ _ = i
  r₁ (ff , j) ⟨ s , k ⟩ (p , ps) = r₁ _ (k p) ps

vecIx : One ▷ ℕ
vecIx = μlx vecNodeIx

Vec'' : Set → ℕ → Set
Vec'' X = ⟦ vecIx ⟧ᵢ (λ _ → X)

vnil'' : ∀ {X} → Vec'' X 0
vnil'' = ⟨ (<> , λ ()) ⟩ , (vv λ ())

vcons'' : ∀ {X n} → X → Vec'' X n → Vec'' X (suc n)
vcons'' x (s , k)
      = ⟨ _ , (λ { (tt , _) → ⟨ (_ , λ ()) ⟩
              ;    (ff , _) → s
              }) ⟩
      ,       (λ { ((tt , _) , _) → x
              ;    ((ff , _) , p) → k p
              })

data Descμ (I : Set) : Set₁ where
  var : I → Descμ I
  σ π : (A : Set)(D : A → Descμ I) → Descμ I
  _×D_ : Descμ I → Descμ I → Descμ I
  κ : Set → Descμ I
  μ : (J : Set) → (J → Descμ (I ⊎ J)) → J → Descμ I

{-
mutual
  ⟦_⟧Dμ : ∀ {I} → Descμ I → (I → Set) → Set
  ⟦ x ⟧Dμ X = ?

  data Dataμ {I J} (F : J → Descμ (I ⊎ J))(X : I → Set) (j : J) : Set where
    ⟨_⟩ : ⟦ F j ⟧Dμ (vv X ⟨?⟩ Dataμ F X) → Dataμ F X j
-}
