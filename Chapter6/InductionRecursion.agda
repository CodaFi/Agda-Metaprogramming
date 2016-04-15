module Chapter6.InductionRecursion where

open import Meta.Basics
open import Meta.Data.Fin
open import Meta.Data.Inductive.ITree
open import Meta.Data.Functor.Container.Indexed

sum prod : (n : ℕ) → (Fin n → ℕ) → ℕ
sum zero _ = 0
sum (suc n) f = f zero + sum n (f ∘ suc)

prod zero _ = 1
prod (suc n) f = f zero * sum n (f ∘ suc)

{-
data FTy : Set where
  fin : ℕ → FTy
  σ π : (S : FTy) (T : Fin {!!} → FTy) → FTy
-}

{-
mutual
  data FTy : Set where
    fin : ℕ → FTy
    σ π : (S : FTy) (T : Fin (# S) → FTy) → FTy

  # : FTy → ℕ
  # (fin x) = x
  # (σ S T) = sum (# S) λ s → # (T s)
  # (π S T) = prod (# S) λ s → # (T s)
-}

fog : ∀ {n} → Fin n → ℕ
fog zero = zero
fog (suc i) = suc (fog i)

mutual
  data FTy : Set where
    fin : ℕ → FTy
    σ π : (S : FTy) (T : FEI S → FTy) → FTy

  FEI : FTy → Set
  FEI (fin x) = Fin x
  FEI (σ S T) = Σ (FEI S) λ s → FEI (T s)
  FEI (π S T) = (s : FEI S) → FEI (T s)

module FRESHLIST (X : Set) (Xeq? : (x x₁ : X) → Dec (x ≃ x₁)) where
  mutual
    data FreshList : Set where
      [] : FreshList
      _,_ : (x : X)(xs : FreshList) {ok : Fresh x xs} → FreshList

    Fresh : X → FreshList → Set
    Fresh x [] = One
    Fresh x (x₁ , xs) with Xeq? x x₁
    Fresh x (x₁ , xs) | tt , _ = Zero
    Fresh x (x₁ , xs) | ff , _ = Fresh x xs

data RecR : Set₁ where
  ⟨⟩ : RecR
  _,_ : (A : Set) (R : A → RecR) → RecR

⟦_⟧RR : RecR → Set
⟦ ⟨⟩ ⟧RR = One
⟦ A , R ⟧RR = Σ A λ a → ⟦ R a ⟧RR

sizeRR : (R : RecR) → ⟦ R ⟧RR → ℕ
sizeRR ⟨⟩ r = 0
sizeRR (A , R) (fst , snd) = suc (sizeRR (R fst) snd)

TyRR : (R : RecR)(r : ⟦ R ⟧RR) → Fin (sizeRR R r) → Set
TyRR ⟨⟩ _ ()
TyRR (A , R) (fst , snd) zero = A
TyRR (A , R) (fst , snd) (suc i) = TyRR (R fst) snd i

vaRR : (R : RecR)(r : ⟦ R ⟧RR)(i : Fin (sizeRR R r)) → TyRR R r i
vaRR ⟨⟩ <> ()
vaRR (A , R) (fst , snd) zero = fst
vaRR (A , R) (fst , snd) (suc i) = vaRR (R fst) snd i

mutual
  data RecL : Set₁ where
    ε : RecL
    _,_ : (R : RecL)(A : ⟦ R ⟧RL → Set) → RecL

  ⟦_⟧RL : RecL → Set
  ⟦ ε ⟧RL = One
  ⟦ R , A ⟧RL = Σ ⟦ R ⟧RL A

sizeRL : RecL → ℕ
sizeRL ε = 0
sizeRL (R , A) = suc (sizeRL R)

TyRL : (R : RecL) → Fin (sizeRL R) → ⟦ R ⟧RL → Set
TyRL ε () <>
TyRL (R , A) zero (fst , snd) = A fst
TyRL (R , A) (suc i) (fst , snd) = TyRL R i fst

vaRL : (R : RecL)(i : Fin (sizeRL R))(r : ⟦ R ⟧RL) → TyRL R i r
vaRL ε () <>
vaRL (R , A) zero (fst , snd) = snd
vaRL (R , A) (suc i) (fst , snd) = vaRL R i fst

TruncRL : (R : RecL) → Fin (sizeRL R) → RecL
TruncRL ε ()
TruncRL (R , A) zero = R
TruncRL (R , A) (suc i) = TruncRL R i

truncRL : (R : RecL)(i : Fin (sizeRL R)) → ⟦ R ⟧RL → ⟦ TruncRL R i ⟧RL
truncRL ε () <>
truncRL (R , A) zero (fst , snd) = fst
truncRL (R , A) (suc i) (fst , snd) = truncRL R i fst

data Manifest {A : Set} : A → Set where
  ⟨_⟩ : (a : A) → Manifest a

mutual
  data RecM : ℕ → Set₁ where
    ε : RecM 0
    _,_ : {n : ℕ} (R : RecM n)(A : ⟦ R ⟧RM → Set) → RecM (suc n)
    _,_∋_ : {n : ℕ} (R : RecM n) (A : ⟦ R ⟧RM → Set)(a : (r : ⟦ R ⟧RM) → A r) → RecM (suc n)

  ⟦_⟧RM : {n : ℕ} → RecM n → Set
  ⟦ ε ⟧RM = One
  ⟦ R , A ⟧RM = Σ ⟦ R ⟧RM A
  ⟦ R , A ∋ a ⟧RM = Σ ⟦ R ⟧RM (Manifest ∘ a)

TyRM : {n : ℕ} (R : RecM n) → Fin n → ⟦ R ⟧RM → Set
TyRM ε () <>
TyRM (R , A) zero (fst , snd) = A fst
TyRM (R , A) (suc i) (fst , snd) = TyRM R i fst
TyRM (R , A ∋ a) zero (fst , snd) = A fst
TyRM (R , A ∋ a) (suc i) (fst , snd) = TyRM R i fst

vaRM : {n : ℕ}(R : RecM n)(i : Fin n)(r : ⟦ R ⟧RM) → TyRM R i r
vaRM ε () r
vaRM (R , A) zero (fst , snd) = snd
vaRM (R , A) (suc i) (fst , snd) = vaRM R i fst
vaRM (R , A ∋ a) zero (fst , snd) = a fst
vaRM (R , A ∋ a) (suc i) (fst , snd) = vaRM R i fst

{-
mutual
  data REx : {n m : ℕ} → RecM n → RecM m → Set₁ where
    ε : REx ε ε

  rfog : ∀ {n m}{R : RecM n}{R₁ : RecM m} (X : REx R R₁) → ⟦ R₁ ⟧RM → ⟦ R ⟧RM
  rfog ε <> = <>
-}

mutual
  data TU : Set where
    Zero' One' Two' : TU
    Σ' Π' : (S : TU)(R : ⟦ S ⟧TU → TU) → TU
    Tree' : (I : TU)(F : ⟦ I ⟧TU → Σ TU λ S →
                         ⟦ S ⟧TU → Σ TU λ P →
                         ⟦ P ⟧TU → ⟦ I ⟧TU)
                    (i : ⟦ I ⟧TU) → TU
  ⟦_⟧TU : TU → Set
  ⟦ Zero' ⟧TU = Zero
  ⟦ One' ⟧TU = One
  ⟦ Two' ⟧TU = Two
  ⟦ Σ' S R ⟧TU = Σ ⟦ S ⟧TU λ s → ⟦ R s ⟧TU
  ⟦ Π' S R ⟧TU = (s : ⟦ S ⟧TU) → ⟦ R s ⟧TU
  ⟦ Tree' I F i ⟧TU = ITree
    ( (λ i → ⟦ fst (F i) ⟧TU)
    ◃ (λ i s → ⟦ fst (snd (F i) s) ⟧TU)
    $ (λ i s p → snd (snd (F i) s) p)
    ) i

Pow : Set₁ → Set₁
Pow X = X → Set

Fam : Set₁ → Set₁
Fam X = Σ Set λ I → I → X

mutual
  data NU (X : Fam Set) : Set where
    U′ : NU X
    El′ : fst X → NU X
    Nat′ : NU X
    Π′ : (S : NU X) (T : ⟦ S ⟧NU → NU X) → NU X

  ⟦_⟧NU : ∀ {X} → NU X → Set
  ⟦_⟧NU { U , El } U′ = U
  ⟦_⟧NU { U , El } (El′ T) = El T
  ⟦ Nat′ ⟧NU = ℕ
  ⟦ Π′ S T ⟧NU = (s : ⟦ S ⟧NU) → ⟦ T s ⟧NU

EMPTY : Fam Set
EMPTY = Zero , λ ()

LEVEL : ℕ → Fam Set
LEVEL zero = (NU EMPTY) , ⟦_⟧NU
LEVEL (suc n) = (NU (LEVEL n)) , ⟦_⟧NU

mutual
  data HU {n} (U : Fin n → Set) : Set where
    U′ : Fin n → HU U
    Nat′ : HU U
    Π′ : (S : HU U) (T : ⟦ S ⟧HU → HU U) → HU U
  ⟦_⟧HU : ∀ {n} {U : Fin n → Set} → HU U → Set
  ⟦_⟧HU {U = U} (U′ i) = U i
  ⟦ Nat′ ⟧HU = ℕ
  ⟦ Π′ S T ⟧HU = (s : ⟦ S ⟧HU) → ⟦ T s ⟧HU

HPREDS : (n : ℕ) → Fin n → Set
HPREDS zero ()
HPREDS (suc n) zero = HU (HPREDS n)
HPREDS (suc n) (suc x) = HPREDS n x

HSET : ℕ → Set
HSET n = HU (HPREDS n)

{-
mutual
  data VV : Set where
    V′ : VV
    Π′ : (S : VV) (T : ⟦ S ⟧VV → VV) → VV
  ⟦_⟧VV : VV → Set
  ⟦ V′ ⟧VV = VV
  ⟦ Π′ S T ⟧VV = (s : ⟦ S ⟧VV) → ⟦ T s ⟧VV
-}

data DS (I J : Set₁) : Set₁ where
  ι : J → DS I J
  σ : (S : Set) (T : S → DS I J) → DS I J
  δ : (H : Set) (T : (H → I) → DS I J) → DS I J

⟦_⟧DS : ∀ {I J} → DS I J → Fam I → Fam J
⟦_⟧DS (ι x) x₁
  = One
  , (λ {<> → x})
⟦_⟧DS (σ S T) x
  = (Σ S λ s → fst (⟦ T s ⟧DS x))
  , (λ { (s , t) → snd (⟦ T s ⟧DS x) t })
⟦_⟧DS (δ H T) (X , xi)
  = (Σ (H → X) λ hx → fst (⟦ T (xi ∘ hx) ⟧DS (X , xi)))
  , (λ { (hx , t) → snd (⟦ T (xi ∘ hx) ⟧DS (X , xi)) t })

idDS : { I : Set₁ } → DS I I
idDS = δ One λ f → ι (f <>)

{-
mutual
  data DataDS {I} (D : DS I I) : Set where
    ⟨_⟩ : fst (⟦ D ⟧DS (DataDS D , ⟦_⟧ds)) → DataDS D
  ⟦_⟧ds : {I : Set₁}{D : DS I I} → DataDS D → I
  ⟦_⟧ds {D = D} ⟨ ds ⟩ = snd (⟦ D ⟧DS (DataDS D , ⟦_⟧ds)) ds
-}

mutual
  data DataDS {I} (D : DS I I) : Set where
    ⟨_⟩ : NoDS D D → DataDS D

  ⟦_⟧ds : {I : Set₁} {D : DS I I} → DataDS D → I
  ⟦_⟧ds {D = D} ⟨ ds ⟩ = DeDS D D ds

  NoDS : {I : Set₁} (D D′ : DS I I) → Set
  NoDS D (ι i) = One
  NoDS D (σ S T) = Σ S λ s → NoDS D (T s)
  NoDS D (δ H T) = Σ (H → DataDS D) λ hd → NoDS D (T (λ h → ⟦ hd h ⟧ds))

  DeDS : {I : Set₁} (D D′ : DS I I) → NoDS D D′ → I
  DeDS D (ι x) <> = x
  DeDS D (σ S T) (s , t) = DeDS D (T s) t
  DeDS D (δ H T) (hd , t) = DeDS D (T (λ h → ⟦ hd h ⟧ds)) t

bindDS : ∀ {I J K} → DS I J → (J → DS I K) → DS I K
bindDS (ι x) U = U x
bindDS (σ S T) U = σ S (λ s → bindDS (T s) U)
bindDS (δ H T) U = δ H (λ f → bindDS (T f) U)

pairDS : ∀ {I J K} (T : DS I J) (U : J → DS I K) {X : Fam I} →
           (t : fst (⟦ T ⟧DS X)) (u : fst (⟦ U (snd (⟦ T ⟧DS X) t) ⟧DS X))
           → fst (⟦ bindDS T U ⟧DS X)
pairDS (ι x) U <> u = u
pairDS (σ S T) U (s , t) u = s , pairDS (T s) U t u
pairDS (δ H T) U {_ , d} (f , t) u = f , (pairDS (T (d ∘ f)) U t u)

{-
coDS : ∀ {I J K} → DS J K → DS I J → DS I K
coDS E D = {!!}
-}

mutual
  data Irish (I : Set₁) : Set₁ where
    ι : Irish I
    κ : Set → Irish I
    π : (S : Set) (T : S → Irish I) → Irish I
    σ : (S : Irish I) (T : Info S → Irish I) → Irish I

  Info : ∀ {I} → Irish I → Set₁
  Info {I} ι = I
  Info (κ A) = ⇑ A
  Info (π S T) = (s : S) → Info (T s)
  Info (σ S T) = Σ (Info S) λ s → Info (T s)

ΠF : (S : Set) {J : S → Set₁} (T : (s : S) → Fam (J s)) → Fam ((s : S) → J s)
ΠF S T = ((s : S) → fst (T s)) , (λ f s → snd (T s) (f s))

ΣF : {I : Set₁} (S : Fam I) {J : I → Set₁} (T : (i : I) → Fam (J i)) → Fam (Σ I J)
ΣF S T = (Σ (fst S) (fst ∘ (T ∘ snd S))) , (λ { (s , t) → snd S s , snd (T (snd S s)) t })

Node : ∀ {I} (T : Irish I) → Fam I → Fam (Info T)
Node ι X = X
Node (κ A) X = A , ↑
Node (π S T) X = ΠF S λ s → Node (T s) X
Node (σ S T) X = ΣF (Node S X) λ iS → Node (T iS) X

IF : Set₁ → Set₁ → Set₁
IF I J = Σ (Irish I) λ T → Info T → J

_$F_ : ∀ {I J} → (I → J) → Fam I → Fam J
f $F (F , i) = F , (f ∘ i)

⟦_⟧IF : ∀ {I J} → IF I J → Fam I → Fam J
⟦ (T , d) ⟧IF X = d $F Node T X

{-
mutual
  data DataIF {I} (F : IF I I) : Set where
    ⟨_⟩ : fst (⟦ F ⟧IF (DataIF F , ⟦_⟧if)) → DataIF F
  ⟦_⟧if : ∀ {I} {F : IF I I} → DataIF F → I
  ⟦_⟧if {F = F} ⟨ ds ⟩ = snd (⟦ F ⟧IF (DataIF F , ⟦_⟧if)) ds
-}

mutual
  data DataIF {I} (F : IF I I) : Set where
    ⟨_⟩ : NoIF F (fst F) → DataIF F

  ⟦_⟧if : ∀ {I} {F : IF I I} → DataIF F → I
  ⟦_⟧if {F = F} ⟨ rs ⟩ = snd F (DelF F (fst F) rs)

  NoIF : ∀ {I} (F : IF I I) (T : Irish I) → Set
  NoIF F ι = DataIF F
  NoIF F (κ A) = A
  NoIF F (π S T) = (s : S) → NoIF F (T s)
  NoIF F (σ S T) = Σ (NoIF F S) λ s → NoIF F (T (DelF F S s))

  DelF : ∀ {I} (F : IF I I) (T : Irish I) → NoIF F T → Info T
  DelF F ι r = ⟦ r ⟧if
  DelF F (κ A) r = ↑ r
  DelF F (π S T) f = λ s → DelF F (T s) (f s)
  DelF F (σ S T) (s , t) = let s′ = DelF F S s in s′ , DelF F (T s′) t

DSIF : ∀ {I J} → DS I J → IF I J
DSIF (ι x) = κ One , (λ _ → x)
DSIF (σ S T) = (σ (κ S) (λ s → fst (DSIF (T (↓ s))))) , (λ { (s , t) → snd (DSIF (T (↓ s))) t })
DSIF (δ H T) = (σ (π H λ _ → ι) (λ f → fst (DSIF (T f)))) , (λ { (f , t) → snd (DSIF (T f)) t })

idIF : ∀ {I} → IF I I
idIF = ι , id

subIF : ∀ {I J} (T : Irish J) (F : IF I J) → IF I (Info T)
subIF ι F = F
subIF (κ A) F = κ A , (λ z → ↑ (↓ z))
subIF (π S T) F = (π S λ s → fst (subIF (T s) F)) , (λ f s → snd (subIF (T s) F) (f s))
subIF (σ S T) F with subIF S F
... | (SF , f) = (σ SF λ sf → fst (subIF (T (f sf)) F)) , (λ { (sf , tf) → f sf , snd (subIF (T (f sf)) F) tf })

colF : ∀ {I J K} → IF J K → IF I J → IF I K
colF (S , x) F with subIF S F
... | TF , f = TF , (x ∘ f)
