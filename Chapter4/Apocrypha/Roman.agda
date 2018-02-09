module Chapter4.Apocrypha.Roman where

open import Meta.Basics
open import Meta.Data.Functor.Container.Indexed
open import Meta.Data.Inductive.ITree
open import Meta.Data.Functor.Container
open import Meta.Data.Inductive.W

-- A Roman Container is a Container decorated by functions that attach input
-- indices to positions and an output index to the shape.
--
-- "The reason Roman containers are so called is that they invoke equality and
-- its mysterious capacity for transubstantiation."
record Roman (I J : Set) : Set₁ where
  constructor SPqr
  field
    S : Set -- A set of shapes
    P : S → Set -- a function taking shapes to arities.
    q : S → J -- a function taking shapes to an index in the family.
    r : (s : S) → P s → I -- a function taking arities to indices.

  -- Lower a Roman Container back to a plain container by dropping the
  -- input/output distinction and the indexing description.
  Plain : Con
  Plain = S ◃ P

  --
  ⟦_⟧R : (I → Set) → (J → Set)
  ⟦_⟧R X j = Σ (Σ S λ s → q s ≃ j) (vv λ s _ → (p : P s) → X (r s p))
Plain = Roman.Plain
⟦_⟧R = Roman.⟦_⟧R

-- We can turn Roman Containers into indexed containers
FromRoman : ∀ {I J} → Roman I J → I ▷ J
FromRoman (SPqr S P q r) = (λ j → Σ S λ s → q s ≃ j) -- Cleverly encodes that the new Roman Container never actually dropped the old indexing structure.
                         ◃ (λ j → P ∘ fst) -- Just drop the proof and grab arities.
                         $ (λ f → r ∘ fst) -- As before, drop the proof and grab the indexing structure.
-- Whose meanings match 'on the nose'.
onTheNose : ∀ {I J} (C : Roman I J) → ⟦ C ⟧R ≃ ⟦ FromRoman C ⟧ᵢ
onTheNose C = refl

-- Similarly, we can convert indexed containers to Roman Containers.
-- Exercise 4.14 (ToRoman): Show how to construct the Roman container isomorphic
-- to a given indexed container and exhibit the isomorphism.
--
-- To project into a Roman container, we re-arrange the signature as follows:
--   S: A product giving us access to the family's index and the operation given at that index.
--   P: Cleverly, this is precisely the data we need to project arities out of the container.
--   q: Just get the family's index out of the product.
--   r: Once again, we set the shapes up with the induction principle and knock
--      them down with the container's indexing description.
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

-- The general purpose tree type for Roman containers looks a lot like the
-- inductive families you find in Agda or the GADTs of Haskell.
--
-- The RomanData type looks a lot like a W-type, albeit festooned with
-- equations.
data RomanData {I} (C : Roman I I) : I → Set where
  _,_ : (s : Roman.S C) → ((p : Roman.P C s) → RomanData C (Roman.r C s p)) → RomanData C (Roman.q C s)

-- Exercise 4.15: Construct a function which takes plain W-type data for a
-- Roman container and marks up each node with the index required of it,
-- using Roman.r.

ideology : ∀ {I} (C : Roman I I) → I → W (Plain C) → W (Plain C ×◃ K◃ I)
ideology C i ⟨ s , k ⟩ = ⟨ ((s , i) , (λ { (tt , p) → ideology C (Roman.r C s p) (k p) ; (ff , ()) })) ⟩

-- Construct a function which takes plain W-type data for a Roman container and
-- marks up each node with the index delivered by it, using Roman.q.

phenomenology : ∀ {I} (C : Roman I I) → W (Plain C) → W (Plain C ×◃ K◃ I)
phenomenology C ⟨ s , k ⟩ = ⟨ ((s , Roman.q C s) , (λ { (tt , snd) → phenomenology C (k snd) ; (ff , ()) })) ⟩

-- Take the W-type interpretation of a Roman container to be the plain data for
-- which the required indices are delivered.

RomanW : ∀ {I} → Roman I I → I → Set
RomanW C i = Σ (W (Plain C)) λ t → phenomenology C t ≃ ideology C i t

-- Now, check that you can extract RomanData from RomanW.

fromRomanW : ∀ {I} (C : Roman I I) {i} → RomanW C i → RomanData C i
fromRomanW C = vv lemma3 C where
  lemma1 : ∀ {I} (C : Roman I I) {s i i' k k'} → _≃_ {X = W (Plain C ×◃ K◃ I)} ⟨ (s , i) , k ⟩ ⟨ (s , i') , k' ⟩ → (i ≃ i')
  lemma1 C₁ refl = refl

  lemma2 : ∀ {I} (C : Roman I I) {s i i' k k'} → _≃_ {X = W (Plain C ×◃ K◃ I)} ⟨ (s , i) , k ⟩ ⟨ (s , i') , k' ⟩ → (k ≃ k')
  lemma2 C₁ refl = refl

  lemma3 : ∀ {I} (C : Roman I I) {i} → (t : W (Plain C)) → phenomenology C t ≃ ideology C i t → RomanData C i
  lemma3 C {i} ⟨ s , k ⟩ g rewrite (i ⟨ lemma1 C g ]= Roman.q C s ∎) = s , λ p → lemma3 C (k p) (cong (_$′ (tt , p)) (lemma2 C g))

-- To go the other way, it is easy to construct the plain tree, but to prove the
-- constraint, you will need to establish equality of functions. Using

postulate
  extensionality : ∀ {S : Set}{T : S → Set} (f g : (s : S) → T s) → ((s : S) → f s ≃ g s) → f ≃ g

-- construct

toRomanW : ∀ {I} (C : Roman I I) {i} → RomanData C i → RomanW C i
toRomanW C (s , x) = {!   !}

--
-- Reflexive Transitive Closure
--

-- Consider the reflexive transitive closure of a relation, also known as the
-- ‘paths in a graph’.
data _** {I : Set} (R : I × I → Set) : I × I → Set where
  ⟨⟩  : {i : I}     → (R **) (i , i)
  _,_ : {i j k : I} → R (i , j) → (R **) (j , k) → (R **) (i , k)
infix 1 _**

-- You can construct the natural numbers as an instance.
NAT : Set
NAT = (Loop **) _ where
  Loop : One × One → Set
  Loop _ = One

-- Exercise 4.17 (monadic operations) Implement these such that the
-- monad laws hold.

one : ∀ {I}{R : I × I → Set} → R -:> (R **)
one (fst , snd) x = x , ⟨⟩

join** : ∀ {I}{R : I × I → Set} → ((R **) **) -:> (R **)
join** _ ⟨⟩        = ⟨⟩
join** i (x , xs) = x ◅◅ join** _ xs where
  _◅◅_ : ∀ {I}{R : I × I → Set}{i j k : I} → (R **) (i , j) → (R **) (j , k) → (R **) (i , k)
  ⟨⟩        ◅◅ ys = ys
  (x , xs) ◅◅ ys = x , (xs ◅◅ ys)

-- We have two ways to formulate a notion of ‘subset’ in type theory. We can
-- define a subset of X as a predicate in
--    X → Set
-- giving a proof-relevant notion of evidence that a given X : X belongs, or we
-- can pick out some elements of X as the image of a function
--    Σ Set λ I → I → X
-- so we have a family of X s indexed by some set.

-- Are these notions the same? That turns out to be a subtle question. A lot
-- turns on the size of X , so we had best be formal about it.

-- In general, X is large.
Pow : Set₁ → Set₁
Pow X = X → Set

Fam : Set₁ → Set₁
Fam X = Σ Set λ I → I → X

-- Exercise 4.18 (small Pow and Fam): Show that, given a suitable notion of
-- propositional equality, Pow ∘ ⇑ and Fam ∘ ⇑ capture essentially the same
-- notion of subset.

p2f : (Pow ∘ ⇑) -:> (Fam ∘ ⇑)
p2f X P = (Σ X (P ∘ ↑)) , (↑ ∘ fst)

f2p : (Fam ∘ ⇑) -:> (Pow ∘ ⇑)
f2p X (I , f) (↑ x) = Σ I λ i → ↓ (f i) ≃ x

-- Exercise 4.19 (functoriality of Pow and Fam): Equip Pow with a contravariant
-- functorial action and Fam with a covariant functorial action.

_$p_ : ∀ {I J} → (J → I) → Pow I → Pow J
f $p P = P ∘ f

_$F_ : ∀ {I J} → (I → J) → Fam I → Fam J
f $F (F , i) = F , (f ∘ i)

-- "Fam Set is Martin-Löf’s notion of a universe, naming a bunch of sets by the
-- elements of some indexing set. Meanwhile, the ‘representation type’ method of
-- describing types concretely in Haskell is just using
-- Pow Set in place of Fam Set. It is good to get used to recognizing when
-- concepts are related just by exchanging Fam and Pow."

-- "Modulo currying and  λ-lifting of parameters, the distinction between
-- Roman I J and our Hancock-style I ▹ J is just that the former represents
-- indexed shapes by a Fam (so Roman.q reads off the shape) whilst the latter
-- uses a Pow (so the shapes pertain to a given index).
-- Both use Fams for positions.

ROMAN : Set → Set → Set1
ROMAN I J = Σ (Fam (⇑ J)) λ { (S , q) → S → Fam (⇑ I) }

HANCOCK : Set → Set → Set1
HANCOCK I J = Σ (Pow (⇑ J)) λ S → Σ J (S ∘ ↑) → Fam (⇑ I)

-- A ‘Nottingham’ indexed container switches the positions to a Pow
-- (see Altenkirch and Morris).

NOTTINGHAM : Set → Set → Set₁
NOTTINGHAM I J = Σ (Pow (⇑ J)) λ S → Σ J (S ∘ ↑) → Pow (⇑ I)

-- which amounts to a presentation of shapes and positions as predicates:
--     NSh : J ! Set
--     NPo : (j : J)!NShj !I !Set

-- For HANCOCK and NOTTINGHAM, we can abstract the whole construction
-- over J , obtaining:
HANCOCK' : Set → Set → Set₁
HANCOCK' I J = J → Fam (Fam (⇑ I))

NOTTINGHAM' : Set → Set → Set₁
NOTTINGHAM' I J = J → Fam (Pow (⇑ I))
