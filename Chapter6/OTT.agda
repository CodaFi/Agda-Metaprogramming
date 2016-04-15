module Chapter6.OTT where

open import Meta.Basics
open import Chapter6.InductionRecursion
open import Meta.Data.Functor.Container.Indexed
open import Meta.Data.Inductive.ITree

{-
data Favourite : (ℕ → ℕ) → Set where
  favourite : Favourite (λ x → zero + x)

data Favourite (f : ℕ → ℕ) : Set where
  favourite : (λ x → zero + x) ≃ f → Favourite f
-}

mutual
  EQ : (X Y : TU) → TU × (⟦ X ⟧TU → ⟦ Y ⟧TU → TU)
  EQ Zero' Zero' = One' , λ _ _ → One'
  EQ One' One' = One' , λ _ _ → One'
  EQ Two' Two' = One' , λ
    { tt tt → One'
    ; ff ff → One'
    ; _ _ → Zero'
    }
  EQ (Σ' S T) (Σ' S' T') = (Σ' (S ↔ S') λ _ →
                            Π' S λ s → Π' S' λ s' → Π' (Eq S s S' s') λ _ →
                            T s ↔ T' s')
                         , (λ { (s , t) (s' , t') →
                                Σ' (Eq S s S' s') λ _ → Eq (T s) t (T' s') t' })
  EQ (Π' S T) (Π' S' T') = (Σ' (S' ↔ S) λ _ →
                            Π' S' λ s' → Π' S λ s → Π' (Eq S' s' S s) λ _ →
                            T s ↔ T' s')
                         , (λ { f f' →
                                  Π' S λ s → Π' S' λ s' → Π' (Eq S s S' s') λ _ →
                                  Eq (T s) (f s) (T' s') (f' s') })
  {- EQ (Tree' I F i) (Tree' I' F' i') = (Σ' (I ↔ I') λ _ → Σ' (Eq I i I' i') λ _ →
                                       Π' I λ i → Π' I' λ i' → Π' (Eq I i I' i') λ _ →
                                       let (S , K) = F i ; S' , K' = F' i'
                                       in Σ' (S ↔ S') λ _ →
                                          Π' S λ s → Π' S' λ s' → Π' (Eq S s S' s') λ _ →
                                          let (P , r) = K s ; (P' , r') = K' s'
                                          in Σ' (P' ↔ P) λ _ →
                                             Π' P' λ p' → Π' P λ p → Π' (Eq P' p' P p) λ _ →
                                             Eq I (r p) I' (r' p'))
                                       , {!teq i i'!} where
                                       teq : (i : ⟦ I ⟧TU) → (i' : ⟦ I' ⟧TU) → ⟦ Tree' I F i ⟧TU → ⟦ Tree' I' F' i' ⟧TU → TU
                                       teq i i' ⟨ s , k ⟩ ⟨ s' , k' ⟩ = ?
                                         = let (S , K) = F i ; (S' , K') = F' i'
                                               (P , r) = K s ; (P' , r') = K' s'
                                           in Σ' (Eq S s S' s') λ _ →
                                             Π' P λ p → Π' P' λ p' → Π' (Eq P p P' p') λ _ →
                                             teq (r p) (r' p') (k p) (k' p') -}
  EQ _ _ = Zero' , λ _ _ → One'

  _↔_ : TU → TU → TU
  X ↔ Y = fst (EQ X Y)

  Eq : (X : TU) (x : ⟦ X ⟧TU) → (Y : TU) (y : ⟦ Y ⟧TU) → TU
  Eq X x Y y = snd (EQ X Y) x y

coe : (X Y : TU) → ⟦ X ↔ Y ⟧TU → ⟦ X ⟧TU → ⟦ Y ⟧TU
postulate
  coh : (X Y : TU) (Q : ⟦ X ↔ Y ⟧TU) (x : ⟦ X ⟧TU) → ⟦ Eq X x Y (coe X Y Q x) ⟧TU
coe X Y Q x = {! !}

postulate
  reflTU : (X : TU) (x : ⟦ X ⟧TU) → ⟦ Eq X x X x ⟧TU

{-
reflTU : (X : TU) (x : ⟦ X ⟧TU) → ⟦ Eq X x X x ⟧TU
reflTU X x = ?
-}

postulate
  RespTU : (X : TU) (P : ⟦ X ⟧TU → TU)
           (x x' : ⟦ X ⟧TU) → ⟦ Eq X x X x' ⟧TU → ⟦ P x ↔ P x' ⟧TU

substTU : (X : TU) (P : ⟦ X ⟧TU → TU)
  (x x' : ⟦ X ⟧TU) → ⟦ Eq X x X x' ⟧TU → ⟦ P x ⟧TU → ⟦ P x' ⟧TU
substTU X P x x' q = coe (P x) (P x') (RespTU X P x x' q)

data Sort : Set where set prop : Sort

IsSet : Sort → Set
IsSet set = One
IsSet prop = Zero


mutual
  data PU (u : Sort) : Set where
    Zero' One' : PU u
    Two' : {_ : IsSet u} → PU u
    Σ' : (S : PU u) (T : ⟦ S ⟧PU → PU u) → PU u
    Π' : (S : PU set) (T : ⟦ S ⟧PU → PU u) → PU u
    Tree' : {_ : IsSet u}
            (I : PU set)
            (F : ⟦ I ⟧PU → Σ (PU set) λ S →
                 ⟦ S ⟧PU → Σ (PU set) λ P →
                 ⟦ P ⟧PU → ⟦ I ⟧PU)
            (i : ⟦ I ⟧PU) → PU u
    Prf' : {_ : IsSet u} → PU prop → PU u

  ⟦_⟧PU : ∀ {u} → PU u → Set
  ⟦ Zero' ⟧PU = Zero
  ⟦ One' ⟧PU = One
  ⟦ Two' ⟧PU = Two
  ⟦ Σ' S T ⟧PU = Σ ⟦ S ⟧PU λ s → ⟦ T s ⟧PU
  ⟦ Π' S T ⟧PU = (s : ⟦ S ⟧PU) → ⟦ T s ⟧PU
  ⟦ Tree' I F i ⟧PU = ITree
    ((λ i → ⟦ fst (F i) ⟧PU)
    ◃ (λ i s → ⟦ fst (snd (F i) s) ⟧PU)
    $ (λ i s p → snd (snd (F i) s) p)
    ) i
  ⟦ Prf' P ⟧PU = ⟦ P ⟧PU

_∧_ : PU prop → PU prop → PU prop
P ∧ Q = Σ' P λ _ → Q

_⇒_ : PU prop → PU prop → PU prop
P ⇒ Q = Π' (Prf' P) λ _ → Q

mutual
  PEQ : (X Y : PU set) → PU prop × (⟦ X ⟧PU → ⟦ Y ⟧PU → PU prop)
  _⇔_ : PU set → PU set → PU prop
  X ⇔ Y = fst (PEQ X Y)

  PEq : (X : PU set) (x : ⟦ X ⟧PU) → (Y : PU set) (y : ⟦ Y ⟧PU) → PU prop
  PEq X x Y y = snd (PEQ X Y) x y

  PEQ (Prf' P) (Prf' Q) = ((P ⇒ Q) ∧ (Q ⇒ P)) , λ _ _ → One'
  PEQ _ _ = Zero' , λ _ _ → One'
