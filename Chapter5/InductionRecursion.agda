module Chapter5.InductionRecursion where

open import Meta.Basics
open import Meta.Data.Fin
open import Meta.Data.Inductive.ITree
open import Meta.Data.Functor.Container.Indexed

-- Finite sums are finite, so we can compute their sizes.
sum prod : (n : ℕ) → (Fin n → ℕ) → ℕ
sum zero _ = 0
sum (suc n) f = f zero + sum n (f ∘ suc)

-- Finite products are finite, so we can compute their sizes.
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

-- A forgetful map from (Fin n) back to ℕ to illustrate induction-recursion.
fog : ∀ {n} → Fin n → ℕ
fog zero = zero
fog (suc i) = suc (fog i)
-}

-- "Where an inductive definition tells us how to perform construction of data
-- incrementally, induction-recursion tells us how to perform
-- construction-with-interpretation incrementally."
mutual
  -- Thus, Construction
  data FTy : Set where
    fin : ℕ → FTy
    σ π : (S : FTy) (T : FEI S → FTy) → FTy

  -- And interpretation.
  FEI : FTy → Set
  FEI (fin x) = Fin x
  FEI (σ S T) = Σ (FEI S) λ s → FEI (T s)
  FEI (π S T) = (s : FEI S) → FEI (T s)

-- The above definition is an important step up in power.  Rather than before
-- where `FTy ∘ #` yielded an unstructured interpretation of a family of sets
-- indexed by ℕ, this time `FTy ∘ FEI` yields a subset Types that have names in
-- FTy while still being small enough to be a set.
--
-- "IR stands for Incredible Ray that shrinks large sets to small encodings of
-- subsets of them.

-- Exercise 5.1 By means of a suitable choice of recursive interpretation, fill
-- the ? with a condition which ensures that FreshLists have distinct elements.
-- Try to make sure that, for any concrete FreshList, ok can be inferred
-- trivially.

module FRESHLIST (X : Set) (Xeq? : (x x₁ : X) → Dec (x ≃ x₁)) where
  mutual
    data FreshList : Set where
      [] : FreshList
      _,_ : (x : X)(xs : FreshList) {ok : Fresh x xs} → FreshList

    -- The distinctness (freshness) guarantee says that.
    Fresh : X → FreshList → Set
    Fresh x [] = One -- There's nothing to do with an x and the empty list.
    Fresh x (x₁ , xs) with Xeq? x x₁ -- Otherwise destruct a decidable eq on head.
    Fresh x (x₁ , xs) | tt , _ = Zero -- We have a match!  It isn't fresh.
    Fresh x (x₁ , xs) | ff , _ = Fresh x xs -- Otherwise try again.

-- "Randy Pollack identified the task of modelling record types as a key early
-- use of induction-recursion , motivated to organise libraries for mathematical
-- structure."
-- In this case, we don't need the full power of the IR Ray because you can
-- get there with Desc and right-nested Σ's.  Essentially, the Σ's give us a way
-- of creating a structure where later fields can depend on earlier fields.
data RecR : Set₁ where
  ⟨⟩ : RecR
  _,_ : (A : Set) (R : A → RecR) → RecR

-- Lower everything back down to Agda's level.
⟦_⟧RR : RecR → Set
⟦ ⟨⟩ ⟧RR = One
⟦ A , R ⟧RR = Σ A λ a → ⟦ R a ⟧RR

-- Exercise 5.2: Show how to compute the size of a record, the define the
-- projections, first of types, then of values.

-- For the sizes of records:
sizeRR : (R : RecR) → ⟦ R ⟧RR → ℕ
sizeRR ⟨⟩ r = 0 -- If we have nothing we're done.
sizeRR (A , R) (fld , rest) = suc (sizeRR (R fld) rest) -- Otherwise we add 1 field and try again.

-- For types:
TyRR : (R : RecR)(r : ⟦ R ⟧RR) → Fin (sizeRR R r) → Set
TyRR ⟨⟩ _ () -- It makes no sense to project the type out of nothing.
TyRR (A , R) (_ , _) zero = A -- If the structure has one field we just project the type of that thing.
TyRR (A , R) (fld , rest) (suc i) = TyRR (R fld) rest i -- Else try again.

-- For values:
vaRR : (R : RecR)(r : ⟦ R ⟧RR)(i : Fin (sizeRR R r)) → TyRR R r i
vaRR ⟨⟩ <> () -- It makes no sense to project a value out of nothing.
vaRR (_ , _) (fld , rest) zero = fld -- If the structure has one field we just project the value out of that.
vaRR (A , R) (fld , rest) (suc i) = vaRR (R fld) rest i -- Else try again.

-- But if you want left-nesting of record types (i.e. Dependent Contexts), you
-- do need the IR Ray.
mutual
  data RecL : Set₁ where
    ε : RecL
    _,_ : (R : RecL)(A : ⟦ R ⟧RL → Set) → RecL

  ⟦_⟧RL : RecL → Set
  ⟦ ε ⟧RL = One
  ⟦ R , A ⟧RL = Σ ⟦ R ⟧RL A

-- Exercise 5.3: Show how to compute the size of a RecL without knowing the
-- individual record.  Show how to interpret a projection as a function from a
-- record, first for types, then values.
sizeRL : RecL → ℕ
sizeRL ε = 0 -- The size of the empty context is zero.
sizeRL (R , A) = suc (sizeRL R) -- Else add one and try again.

-- For Types:
TyRL : (R : RecL) → Fin (sizeRL R) → ⟦ R ⟧RL → Set
TyRL ε () <> -- It makes no sense to project a type out of the empty structure.
TyRL (R , A) zero (idx , _) = A idx -- If the structure has one field we project it out by indexing with the field.
TyRL (R , A) (suc i) (idx , _) = TyRL R i idx -- Else try again.

-- For values:
vaRL : (R : RecL)(i : Fin (sizeRL R))(r : ⟦ R ⟧RL) → TyRL R i r
vaRL ε () <> -- It makes no sense to project a value out of the empty structure.
vaRL (R , A) zero (_ , fld) = fld -- If the structure has one field just project the value out.
vaRL (R , A) (suc i) (idx , snd) = vaRL R i idx

-- Exercise 5.4: Show how to truncate a record signature from a given field and
-- compute the corresponding projection on structures.

-- To truncate a context:
TruncRL : (R : RecL) → Fin (sizeRL R) → RecL
TruncRL ε () -- It makes no sense to truncate the empty context.
TruncRL (R , A) zero = R -- For a context with a single part, yield it.
TruncRL (R , A) (suc i) = TruncRL R i -- Else try again.

-- To project out of a truncation:
truncRL : (R : RecL)(i : Fin (sizeRL R)) → ⟦ R ⟧RL → ⟦ TruncRL R i ⟧RL
truncRL ε () <> -- How did we get here?
truncRL (R , A) zero (fst , snd) = fst -- For a singleton context, give up the subpart.
truncRL (R , A) (suc i) (fst , snd) = truncRL R i fst -- Else try again.

-- A Manifest is a record whose values are computed from earlier fields.  "It is
-- rather like allowing definitions in contexts."
data Manifest {A : Set} : A → Set where
  ⟨_⟩ : (a : A) → Manifest a

mutual
  -- "I index by size, to save on measuring."
  data RecM : ℕ → Set₁ where
    ε : RecM 0 -- The empty manifest.
    _,_ : {n : ℕ} (R : RecM n)(A : ⟦ R ⟧RM → Set) → RecM (suc n) -- Old-school fields
    _,_∋_ : {n : ℕ} (R : RecM n) (A : ⟦ R ⟧RM → Set)(a : (r : ⟦ R ⟧RM) → A r) → RecM (suc n) -- A definition.

  ⟦_⟧RM : {n : ℕ} → RecM n → Set
  ⟦ ε ⟧RM = One
  ⟦ R , A ⟧RM = Σ ⟦ R ⟧RM A
  ⟦ R , A ∋ a ⟧RM = Σ ⟦ R ⟧RM (Manifest ∘ a)

-- Exercise 5.5: Implement projection for RecM.

-- For types:
TyRM : {n : ℕ} (R : RecM n) → Fin n → ⟦ R ⟧RM → Set
-- Makes no sense to project out of nothing.
TyRM ε () <>
-- If the structure has one field we project it out by indexing with the field
TyRM (R , A) zero (idx , _) = A idx
-- Else try again.
TyRM (R , A) (suc i) (idx , _) = TyRM R i idx
-- If the structure has one definition we project it out by indexing with the field.
TyRM (R , A ∋ a) zero (idx , _) = A idx
-- Else try again.
TyRM (R , A ∋ a) (suc i) (idx , _) = TyRM R i idx

-- For values:
vaRM : {n : ℕ}(R : RecM n)(i : Fin n)(r : ⟦ R ⟧RM) → TyRM R i r
-- Makes no sense to project out of nothing.
vaRM ε () r
-- If the structure has one field, project it out.
vaRM (R , A) zero (_ , fld) = snd
-- Else try again.
vaRM (R , A) (suc i) (idx , _) = vaRM R i idx
-- If the structure has one manifest field, project it out by feeding it what it depends on.
vaRM (R , A ∋ a) zero (idx , _) = a idx
-- Else try again.
vaRM (R , A ∋ a) (suc i) (idx , _) = vaRM R i idx

{-
mutual
  data REx : {n m : ℕ} → RecM n → RecM m → Set₁ where
    ε : REx ε ε

  rfog : ∀ {n m}{R : RecM n}{R₁ : RecM m} (X : REx R R₁) → ⟦ R₁ ⟧RM → ⟦ R ⟧RM
  rfog ε <> = <>
-}

mutual
  -- Conor's Favorite Universe Featuring:
  data TU : Set where
    -- A scattering of base types.
    Zero' One' Two' : TU
    -- Dependent pairs (and functions).
    Σ' Π' : (S : TU)(R : ⟦ S ⟧TU → TU) → TU
    -- And Petersson-Synek Trees.
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

-- Unfortunately, because this is an inductive-recursive structure in and of
-- itself: you can't use the IR Ray on an IR Ray.

Pow : Set₁ → Set₁
Pow X = X → Set

Fam : Set₁ → Set₁
Fam X = Σ Set λ I → I → X

mutual
  -- A predicative hierarchy of small universes built using induction-recursion.
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

-- Universes can be "jacked up" as far as we like.

EMPTY : Fam Set
EMPTY = Zero , λ ()

LEVEL : ℕ → Fam Set
LEVEL zero = (NU EMPTY) , ⟦_⟧NU
LEVEL (suc n) = (NU (LEVEL n)) , ⟦_⟧NU

mutual
  -- To eliminate redudancy of lower universes, we parametrize the universe by a
  -- de Bruijin indexed collection of the previous universes.
  data HU {n} (U : Fin n → Set) : Set where
    U′ : Fin n → HU U
    Nat′ : HU U
    Π′ : (S : HU U) (T : ⟦ S ⟧HU → HU U) → HU U
  ⟦_⟧HU : ∀ {n} {U : Fin n → Set} → HU U → Set
  ⟦_⟧HU {U = U} (U′ i) = U i
  ⟦ Nat′ ⟧HU = ℕ
  ⟦ Π′ S T ⟧HU = (s : ⟦ S ⟧HU) → ⟦ T s ⟧HU

-- "To finish the job, we must build the collections of levels to hand to HU. At
-- each step, level zero is the new top level, built with a fresh appeal to HU,
-- but lower levels can be projected from the previous collection."

HPREDS : (n : ℕ) → Fin n → Set
HPREDS zero ()
HPREDS (suc n) zero = HU (HPREDS n)
HPREDS (suc n) (suc x) = HPREDS n x

HSET : ℕ → Set
HSET n = HU (HPREDS n)

{- rejected.
mutual
  data VV : Set where
    V′ : VV
    Π′ : (S : VV) (T : ⟦ S ⟧VV → VV) → VV
  ⟦_⟧VV : VV → Set
  ⟦ V′ ⟧VV = VV
  ⟦ Π′ S T ⟧VV = (s : ⟦ S ⟧VV) → ⟦ T s ⟧VV
-}

-- An encoding of allowed inductive-recursive things [Dybjer and Setzer 1999].
-- The encoding is as follows:
--   ∘ Describe one node of inductive recursive types in the manner of RecR but
--     where each J-value read gives us a way of reading off I values.
data DS (I J : Set₁) : Set₁ where
  ι : J → DS I J                                -- no more fields
  σ : (S : Set) (T : S → DS I J) → DS I J       -- ordinary field
  δ : (H : Set) (T : (H → I) → DS I J) → DS I J -- child field.

-- A DS is a functor.
--
-- "In each case, we must say which set is being encoded and how to read off a J
-- from a value in that set.
⟦_⟧DS : ∀ {I J} → DS I J → Fam I → Fam J
-- The ι constructor carries exactly the j required. The other two specify a
-- field in the node structure, from which the computation of the J gains some
-- information.
⟦_⟧DS (ι x) x₁
  = One
  , (λ {<> → x})
-- The σ specifies a field of type S, and the rest of the structure may depend
-- on a value of type S.
⟦_⟧DS (σ S T) x
  = (Σ S λ s → fst (⟦ T s ⟧DS x))
  , (λ { (s , t) → snd (⟦ T s ⟧DS x) t })
-- The δ case is the clever bit.  It specifies a place for an H-indexed bunch of
-- children, and even through we do not fix what set represents the children, we
-- do know that they allow us to read off an I.  Correspondingly, the rest of
-- the structure can at least depend on knowing a function in H → I which gives
-- access to the interpretation of the children.  Once we plugin a specific
-- (X, xi) : Fam I, we represent the field by the small function space
-- hx : H → X, then the composition xi ∘ hx tells us how to compute the large
-- meaning of each child."
⟦_⟧DS (δ H T) (X , xi)
  = (Σ (H → X) λ hx → fst (⟦ T (xi ∘ hx) ⟧DS (X , xi)))
  , (λ { (hx , t) → snd (⟦ T (xi ∘ hx) ⟧DS (X , xi)) t })

-- Exercise 5.10: A morphism form (X, xi) to (Y, yi) in Fam I is a function
-- f : X → Y such that xi = yi ∘ f.  Construct a code for the identity functor
-- on Fam I such that ⟦ idDS ⟧DS ≅ id.
idDS : { I : Set₁ } → DS I I
idDS = δ One λ f → ι (f <>)

{- -- fails positivity check and termination check.
mutual
  data DataDS {I} (D : DS I I) : Set where
    ⟨_⟩ : fst (⟦ D ⟧DS (DataDS D , ⟦_⟧ds)) → DataDS D
  ⟦_⟧ds : {I : Set₁}{D : DS I I} → DataDS D → I
  ⟦_⟧ds {D = D} ⟨ ds ⟩ = snd (⟦ D ⟧DS (DataDS D , ⟦_⟧ds)) ds
-}

mutual
  -- We get out of this jam by inlining the interpretation.
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
