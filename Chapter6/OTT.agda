module Chapter6.OTT where

open import Meta.Basics
open import Meta.Data.Inductive.Recursion
open import Meta.Data.Functor.Container.Indexed
open import Meta.Data.Inductive.ITree

{-
"We cannot have an equality which is both extensional and decidable."

Or, that is to say, in order to give up either extensionality or decidability
you wind up in one of two bad places:
1) Either you give up extensionality and are right back where you started
  (hence the definition below): trapped in a framework in which you can't
  prove anything more interesting than the ensemble of constructors you have
  and some equally terrible definition of substitution will allow.  This is
  because `favorite` below is an "intensional Predicate" whose only canonical
  form is `λ x → zero + x`.
2) Or you give up decidability and, well, no.  Don't do that.

The trouble here is binders.  If all the Favourite type chose to do with its
parameter was apply it to arguments, extensionality would come naturally.  But
to decide equality under binders in general requires a framework for computing
under them that we simply don't have (yet) with vanilla refl.

data Favourite : (ℕ → ℕ) → Set where
  favourite : Favourite (λ x → zero + x)

If we try again taking some fictitious extensional equality ≃ then lift things
into Favorite, then Favorite becomes just as extensional as the chosen equality.

"If q′ : f ≃ g, then we can transport favorite q from Favorite f to Favorite g,
returning, not the original data but

  favourite ((λ x → zero +ℕ x) =[ q ⟩ f =[ q′ ⟩ q ∎)

with a modified proof."

data Favourite (f : ℕ → ℕ) : Set where
  favourite : (λ x → zero + x) ≃ f → Favourite f
-}

-- The mechanism that allows us a more general yet extensional equality of terms
-- is Observational Equality, where essentially we use a set of local
-- mini-propositional equalities on the result of inspecting the types and
-- values of terms.

-- "Inasmuch as types depend on values, we shall also need to say when values
-- are equal.  There is no reasn to presume that we shall be interested only to
-- consider the equality of values in types which are judgmentally equal, for we
-- know that judgmental equality is too weak to recognize the sameness of some
-- types whose values are interchangeable.  Correspondingly, let us weaken our
-- requirement for the formation of value equalities and have a heterogeneous
-- equality, Eq X x Y y.  We have some options for how to do that:
--
--   ∘ We could add the requirement X ↔ Y to the formation rule for Eq
--   ∘ We could allow the formation of any Eq X x Y y, but ensure that it holds
--     only if X ↔ Y.
--   ∘ We could allow the formation of any Eq X x Y y, but ensure that proofs of
--     such equations are useless information unless X ↔ Y."
--
-- Spoiler: We choose the third.

mutual -- By recursion on types in TU:
  EQ : (X Y : TU) → TU × (⟦ X ⟧TU → ⟦ Y ⟧TU → TU)
  -- "Base types equal only themselves, and we need no help to transport a value
  -- from a type to itself.""
  EQ Zero' Zero' = One' , λ _ _ → One'
  EQ One' One' = One' , λ _ _ → One'
  EQ Two' Two' = One' , λ
    { tt tt → One'
    ; ff ff → One'
    ; _ _ → Zero'
    }
  -- Σ-types+
  EQ (Σ' S T) (Σ' S' T') = (Σ' (S ↔ S') λ _ → -- are interchangeable if
                            Π' S λ s → Π' S' λ s' → Π' (Eq S s S' s') λ _ →
                            T s ↔ T' s')
                         , (λ { (s , t) (s' , t') → -- their components are.
                                Σ' (Eq S s S' s') λ _ → Eq (T s) t (T' s') t' })
  -- Equality of Π-types is straightforward, then.   Because Π-types
  EQ (Π' S T) (Π' S' T') = (Σ' (S' ↔ S) λ _ → -- are interchangeable if
                            Π' S' λ s' → Π' S λ s → Π' (Eq S' s' S s) λ _ →
                            T s ↔ T' s')
                         , (λ { f f' → -- their projected components are.
                                  Π' S λ s → Π' S' λ s' → Π' (Eq S s S' s') λ _ →
                                  Eq (T s) (f s) (T' s') (f' s') })
  -- Equality of Tree-types procedes structurally.  That is, Tree-types
  EQ (Tree' I F i) (Tree' I' F' i')
    = (Σ' (I ↔ I') λ _ → Σ' (Eq I i I' i') λ _ → -- are interchangeable if
         Π' I λ i → Π' I' λ i' → Π' (Eq I i I' i') λ _ →
         let (S , K) = F i ; S' , K' = F' i'
         in Σ' (S ↔ S') λ _ → -- we get equal shapes here
            Π' S λ s → Π' S' λ s' → Π' (Eq S s S' s') λ _ →
            let (P , r) = K s ; (P' , r') = K' s'
            in Σ' (P' ↔ P) λ _ → -- and equal shapes there
               Π' P' λ p' → Π' P λ p → Π' (Eq P' p' P p) λ _ →
               Eq I (r p) I' (r' p')) --
         , teq i i' where
         -- Demands equal subtrees of the two given terms in TU
         teq : (i : ⟦ I ⟧TU) → (i' : ⟦ I' ⟧TU) → ⟦ Tree' I F i ⟧TU → ⟦ Tree' I' F' i' ⟧TU → TU
         teq i i' ⟨ s , k ⟩ ⟨ s' , k' ⟩
           = let (S , K) = F i ; (S' , K') = F' i'
                 (P , r) = K s ; (P' , r') = K' s'
             in Σ' (Eq S s S' s') λ _ → -- Subtrees are interchangeable when
               Π' P λ p → Π' P' λ p' → Π' (Eq P p P' p') λ _ → -- the shapes and points match and
               teq (r p) (r' p') (k p) (k' p') -- when further subtrees are interchangeable.
  -- Otherwise ex falso.  After all, if you got this far, you deserve a medal.
  EQ _ _ = Zero' , λ _ _ → One'

  -- Extract the type realized by the observational equality above.
  _↔_ : TU → TU → TU
  X ↔ Y = fst (EQ X Y)

  -- Extract the equality realized by the observational equality above.
  Eq : (X : TU) (x : ⟦ X ⟧TU) → (Y : TU) (y : ⟦ Y ⟧TU) → TU
  Eq X x Y y = snd (EQ X Y) x y

-- Coercion that realises equality as transportation.
coe : (X Y : TU) → ⟦ X ↔ Y ⟧TU → ⟦ X ⟧TU → ⟦ Y ⟧TU
postulate
  coh : (X Y : TU) (Q : ⟦ X ↔ Y ⟧TU) (x : ⟦ X ⟧TU) → ⟦ Eq X x Y (coe X Y Q x) ⟧TU
coe Zero' Zero' <> x = x
coe Zero' One' () x
coe Zero' Two' () x
coe Zero' (Σ' Y R) () x
coe Zero' (Π' Y R) () x s
coe Zero' (Tree' Y F i) () x
coe One' Zero' () x
coe One' One' <> x = x
coe One' Two' () x
coe One' (Σ' Y R) () x
coe One' (Π' Y R) () x s
coe One' (Tree' Y F i) () x
coe Two' Zero' () x
coe Two' One' () x
coe Two' Two' <> x = x
coe Two' (Σ' Y R) () x
coe Two' (Π' Y R) () x s
coe Two' (Tree' Y F i) () x
coe (Σ' X R) Zero' () x
coe (Σ' X R) One' () x
coe (Σ' X R) Two' () x
coe (Σ' X XT) (Σ' Y YT) (TYEQ , TEQ) (x , y)
  = let x′ = coe X Y TYEQ x
        y′ = coe (XT x) (YT x′) (TEQ x x′ (coh X Y TYEQ x)) y
    in (x′ , y′)
coe (Σ' X R) (Π' Y R₁) () x s
coe (Σ' X R) (Tree' Y F i) () x
coe (Π' X R) Zero' () x
coe (Π' X R) One' () x
coe (Π' X R) Two' () x
coe (Π' X R) (Σ' Y R₁) () x
coe (Π' XL XR) (Π' YL YR) (LEQ , REQ) f x′
  = let x = coe YL XL LEQ x′
        y = f x
    in coe (XR x) (YR x′) (REQ x′ x (coh YL XL LEQ x′)) y
coe (Π' X R) (Tree' Y F i) () x
coe (Tree' X F i) Zero' () x
coe (Tree' X F i) One' () x
coe (Tree' X F i) Two' () x
coe (Tree' X F i) (Σ' Y R) () x
coe (Tree' X F i) (Π' Y R) () x s
coe (Tree' I F i) (Tree' I′ F′ i′) (_ , (TREQ , IEQ)) x = tcoe i i′ TREQ x
  where
    -- This is Conor's
    tcoe : (i : ⟦ I ⟧TU)(i′ : ⟦ I′ ⟧TU)(iq : ⟦ Eq I i I′ i′ ⟧TU) → ⟦ Tree' I F i ⟧TU → ⟦ Tree' I′ F′ i′ ⟧TU
    tcoe i i' ieq ⟨ s , k ⟩ =
      let  (S , K) = F i ; (S' , K') = F′ i'
           (SQ , TQ) = IEQ i i' ieq
           s' = coe S S' SQ s ; sh = coh S S' SQ s
           (P , r) = K s ; (P' , r') = K' s'
           (STEQ , rq) = TQ s s' sh
      in ⟨ (s' , λ p' →
            let p = coe P' P STEQ p'
                peq = coh P' P STEQ p'
            in  tcoe (r p) (r' p') (rq p' p peq) (k p)) ⟩

-- "If you look at the definition of EQ quite carefully, you will notice that we
-- did not use all of the types in TU to express equations. There is never any
-- choice about how to be equal, so we need never use Two0; meanwhile, we can
-- avoid expressing tree equality as itself a tree just by using structural
-- recursion. As a result, the only constructor pattern matching coe need ever
-- perform on proofs is on pairs, which is just sugar for the lazy use of
-- projections. Correspondingly, the only way coercion of canonical values
-- between canonical types can get stuck is if those types are conspicuously
-- different. Although we postulated coherence, no computation which relies on
-- it is strict in equality proofs, so it is no source of blockage.
--
-- The only way a closed coercion can get stuck is if we can prove a false
-- equation. The machinery works provided the theory is consistent, but we can
-- prove no equations which do not also hold in extensional type theories which
-- are known to be consistent. In general, we are free to assert consistent
-- equations."
postulate
  reflTU : (X : TU) (x : ⟦ X ⟧TU) → ⟦ Eq X x X x ⟧TU

{- Exercise 6.2: Try proving this; where do you get stuck?
reflTU : (X : TU) (x : ⟦ X ⟧TU) → ⟦ Eq X x X x ⟧TU
reflTU X x = ?
-}

postulate
  -- Homogeneous equations between values are made useful just by asserting that
  -- predicates respect them. We recover the Leibniz property.
  RespTU : (X : TU) (P : ⟦ X ⟧TU → TU)
           (x x' : ⟦ X ⟧TU) → ⟦ Eq X x X x' ⟧TU → ⟦ P x ↔ P x' ⟧TU

substTU : (X : TU) (P : ⟦ X ⟧TU → TU)
  (x x' : ⟦ X ⟧TU) → ⟦ Eq X x X x' ⟧TU → ⟦ P x ⟧TU → ⟦ P x' ⟧TU
substTU X P x x' q = coe (P x) (P x') (RespTU X P x x' q)

-- We can express the observation that all of our proofs belong to lazy types by
-- splitting our universe into two Sorts, corresponding to sets and
-- propositions, embedding the latter explicitly into the former with a new
-- set-former, Prf'.

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


-- Exercise 6.3 (observational propositional equality): Reconstruct the
-- definition of observational equality in this more refined setting. Take
-- equality of propositions to be mutual implication and equality of proofs to
-- be trivial: after all, equality for proofs of the atomic Zero' and One'
-- propositions are trivial.

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
  -- more code goes here
  PEQ _ _ = Zero' , λ _ _ → One'
