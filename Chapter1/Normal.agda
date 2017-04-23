module Chapter1.Normal where

open import Meta.Basics
open import Agda.Primitive

open import Meta.Data.Fin
open import Meta.Data.Vector
open import Meta.Data.Monoid
open import Meta.Control.Applicative
open import Meta.Control.Traversable

-- A Normal Functor is given, up to isomorphism, by:
record Normal : Set₁ where
  constructor _/_
  field
    Shape : Set -- a set of shapes
    size : Shape → ℕ -- and a function which assigns to each shape a size.
  ⟦_⟧ℕ : Set → Set -- Normal functors can be interpreted as dependent vectors.
  ⟦_⟧ℕ X = Σ Shape λ s → Vec X (size s)
open Normal public
infixr 0 _/_

-- Vectors are normal functors with a unique shape.
VecN : ℕ → Normal
VecN n = One / const n

-- Lists are normal functors whose shape is their size.
ListN : Normal
ListN = ℕ / id

-- "But let us not get ahead of ourselves. We can build a kit for normal
-- functors cor- responding to the type constructors that we often define, then
-- build up composite structures."

-- The normal functor for any particular point in a type is given by that point
-- and a singular shape: that of the point which has size 0.
Kℕ : Set → Normal
Kℕ A = A / const 0

-- The identity can be lifted to vectors quite easily.
IKℕ : Normal
IKℕ = VecN 1

-- The sum of normal functors is the sum of the shapes and a selector for sizes.
_+N_ : Normal → Normal → Normal
(ShF / szF) +N (ShG / szG) = (ShF ⊎ ShG) / vv szF ⟨?⟩ szG

-- The product of normal functors is the product of shapes and the sum of sizes.
_×N_ : Normal → Normal → Normal
(ShF / szF) ×N (ShG / szG) = (ShF × ShG) / vv λ f g → szF f + szG g

-- If you "lower" 2 normal functors to their vector representation, you
-- should be able to interpret the sum of vectors as a vector of the sum
-- of the normals.
nInj : ∀ { X } (F G : Normal) → ⟦ F ⟧ℕ X ⊎ ⟦ G ⟧ℕ X → ⟦ F +N G ⟧ℕ X
nInj F G (tt , (ShF , xs)) = (tt , ShF) , xs
nInj F G (ff , (ShG , xs)) = (ff , ShG) , xs

-- nInj is also surjective.
nCase : ∀ { X } F G (s :  ⟦ F +N G ⟧ℕ X) → nInj F G ⁻¹ s
nCase F G ((tt , ShF) , xs) = from (tt , (ShF , xs))
nCase F G ((ff , ShG) , xs) = from (ff , (ShG , xs))

--
nOut : ∀ { X }(F G : Normal) → ⟦ F +N G ⟧ℕ X → ⟦ F ⟧ℕ X ⊎ ⟦ G ⟧ℕ X
nOut F G xs' with nCase F G xs'
nOut F G . (nInj F G xs) | from xs = xs

-- The product of vectors is the vector of inner products
nPair : ∀ { X }(F G : Normal) →  ⟦ F ⟧ℕ X × ⟦ G ⟧ℕ X → ⟦ F ×N G ⟧ℕ X
nPair F G ((ShFx , fs) , (ShGx , gs)) = (ShFx , ShGx) , (fs ++ gs)

-----------------------------------------------------------
-- Exercise 1.14
--
-- "While you are in this general area, construct (from readily available
-- components) the usual monoid structure for our normal presentation of lists."
-----------------------------------------------------------

split : ∀ m n {X}(xs : Vec X (m + n)) → (vv (_++_ {m}{n}{X})) ⁻¹ xs
split zero n xs = from (⟨⟩ , xs)
split (suc m) n (x , xs) with split m n xs
split (suc m) n (x , .(ys ++ zs)) | from (ys , zs) = from ((x , ys) , zs)

nSplit : ∀ {X}(F G : Normal)(fgx : ⟦ F ×N G ⟧ℕ X) → nPair F G ⁻¹ fgx
nSplit F G ((f , g) , xs) with split (size F f) (size G g) xs
nSplit F G ((f , g) , .(ys ++ zs)) | from (ys , zs) = from ((f , ys) , (g , zs))

concatSurjectivity : forall {m n : ℕ} {X} → (x : Vec X (m + n)) → (vv λ (u : Vec X m) (v : Vec X n) → u ++ v) ⁻¹ x
concatSurjectivity {zero} v = from (⟨⟩ , v)
concatSurjectivity {suc m} (x , v) with concatSurjectivity {m} v
concatSurjectivity {suc m} (x , .(u ++ w)) | from (u , w) = from ((x , u) , w)

unAppend : ∀ m n {X} → (xsys : Vec X (m + n)) → (vv _++_ {m}{n}) ⁻¹ xsys
unAppend zero n ys = from (⟨⟩ , ys)
unAppend (suc m) n (x , xsys) with unAppend m n xsys
unAppend (suc m) n (x , .(xs ++ ys)) | from (xs , ys) = from ((x , xs) , ys)

instance
  listNMonoid : {X : Set} → Monoid (⟦ ListN ⟧ℕ X)
  listNMonoid = record
    { ε = (zero , ⟨⟩)
    ; _•_ = vv λ xn xs → vv λ yn ys → (xn + yn) , (xs ++ ys)
    }
-----------------------------------------------------------
-----------------------------------------------------------

listNMonoidOK : {X : Set} → MonoidOK (⟦ ListN ⟧ℕ X) {{listNMonoid}}
listNMonoidOK {X} = record
  { absorbL = λ _ → refl
  ; absorbR = vv ++<>
  ; assoc = vv <+>
  } where
    ++<> : ∀ n (xs : Vec X n) → ((n , xs) • ε) ≃ (n , xs)
    ++<> zero ⟨⟩ = refl
    ++<> (suc n) (x , xs) = cong (vv λ m ys → suc m , (x , ys)) (++<> n xs)

    <+> : ∀ n (t : Vec X (size ListN n))
      (y z : ⟦ ListN ⟧ℕ X) →
      ((n , t) • y) • z ≃ (n , t) • (y • z)
    <+> zero ⟨⟩ _ _ = refl
    <+> (suc n) (x , xs) (i , ys) (j , zs) = subst (<+> n xs (i , ys) (j , zs))
       (vv λ m ws → _≃_ {_}{⟦ ListN ⟧ℕ X}
         (suc ((n + i) + j) , (x , ((xs ++ ys) ++ zs))) (suc m , (x , ws)))
       refl

-- Normal functors are traversable because Vectors are traversable.
instance
  normalTraversable : (F : Normal) → Traversable ⟦ F ⟧ℕ
  normalTraversable F = record
    { traverse = λ { {{aG}} f (sh , xs) → pure {{aG}} (_,_ sh) ⍟ traverse f xs } }


-- "We have already seen that the identity functor VecN 1 is Normal, but can we
-- define composition?"
--
-- Yeah.  Yeah we can.
_◦N_ : Normal → Normal → Normal
F ◦N (ShG / szG) =  ⟦ F ⟧ℕ ShG / crush {{normalTraversable F}} szG

-- The size of a traversable thing can be obtained using the Monoidness of ℕ.
sizeT : ∀ {F}{{TF : Traversable F}}{X} → F X → ℕ
sizeT {F} = crush {F = F} (λ _ → 1)

-- And hey, if you can get its size that way, you can make a Normal.
normalT : ∀ F {{TF : Traversable F}} → Normal
normalT F = F One / (sizeT {F = F})

--
shapeT : ∀ {F}{{TF : Traversable F}}{X} → F X → F One
shapeT {F}{{TF}} = traverse (λ _ → <>)

one : ∀ {X} → X → ⟦ ListN ⟧ℕ X
one x = 1 , (x , ⟨⟩)

contentsT : ∀ {F}{{TF : Traversable F}}{X} → F X → ⟦ ListN ⟧ℕ X
contentsT {F} {{TF}} {X} = crush {{TF}}{{listNMonoid}} one

_⟶N_ : Normal → Normal → Set
F ⟶N G = (s : Shape F) → ⟦ G ⟧ℕ (Fin (size F s))

nMorph : ∀ {F G} → F ⟶N G → ∀ {X} → ⟦ F ⟧ℕ X → ⟦ G ⟧ℕ X
nMorph f (s , xs) with f s
nMorph f (x , xs) | (s' , is) = s' , vmap (proj xs) is

morphN : ∀ {F G} → (∀ {X} → ⟦ F ⟧ℕ X → ⟦ G ⟧ℕ X) → F ⟶N G
morphN f s = f (s , tabulate id)

{-
toNormal : ∀ {F}{{TF : Traversable F}} → TraversableOKP F → ∀ {X} → F X → ⟦ normalT F ⟧ℕ X
toNormal tokf fx = shapeT fx , subst (lengthContentsSizeShape tokf fx) (Vec _) (snd (contentsT fx))
  where
    lengthContentsSizeShape : ∀ {F} {{TF : Traversable F}} → TraversableOKP F → ∀ {X} (fx : F X) → fst (contentsT fx) ≃ sizeT (shapeT fx)
    lengthContentsSizeShape tokF fx =
      fst (contentsT fx)
        ⟨ TraversableOKP.lawPHom tokF {{monoidApplicative {{_}}}} {{monoidApplicative {{_}}}} fst one (monoidApplicativeHom {{_}}{{_}} fst {{_}}) fx ]=
      sizeT fx
        ⟨ TraversableOKP.lawPCo tokF {{monoidApplicative {{_}}}} {{applicativeId}} (λ _ → 1) (λ _ → <>) fx ]=
      sizeT {{_}} (shapeT fx)
        ∎
-}

_⊗_ : Normal → Normal → Normal
(ShF / szF) ⊗ (ShG / szG) = (ShF × ShG) / λ s → szF (fst s) * szG (snd s)

*-comm : ∀ m n → m * n ≃ n * m
*-comm m n = {!   !}

swap : (F G : Normal) → (F ⊗ G) ⟶N (G ⊗ F)
swap F G (ShF , ShG) rewrite *-comm (size F ShF) (size G ShG) = (ShG , ShF) , allFin _

drop : (F G : Normal) → (F ⊗ G) ⟶N (F ◦N G)
drop F G (ShF , ShG) = (ShF , (vec ShG)) , {! k  !}
 where
  k : {n m : ℕ} → n ≃ m → Vec (Fin m) n
  k {n} {.n} refl = tabulate id

fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ℕ X}{{listNMonoid}}{ℕ}{{sumMonoid}} fst
fstHom = record
  { respε = refl
  ; resp• = λ _ _ → refl
  }

Batch : Set → Set → Set
Batch X Y = Σ ℕ λ n → Vec X n → Y

batchApplicative : {X : Set} → Applicative (Batch X)
batchApplicative {X} = record
  { pure = λ y → (0 , λ _ → y)
  ; _⍟_ = app
  } where
    app : {S T : Set} → Batch X (S → T) → Batch X S → Batch X T
    app (n , f) (m , g) = (n + m) , (λ xs → let ss = chop n xs in f (fst ss) (g (snd ss)))

batcher : ∀ {F} {{TF : Traversable F}} → F One → ∀ {X} → Batch X (F X)
batcher {F} {{TF}} sF {X} = traverse {F} {{TF}} {Batch X} {{batchApplicative}} (λ _ → 1 , λ { (x , _) → x }) sF

{-
coherence : ∀ {F} {{TF : Traversable F}} {X} → TraversableOKP F
            → (sF : F One) →
               fst (batcher {F} {{TF}} sF {X}) ≃
               traverse {F} {{TF}} {λ _ → ℕ} {One} {One} {{monoidApplicative {{sumMonoid}}}} (λ _ → 1) sF
coherence {F} {{TF}} {X} tokF u = {!   !}

   fst (traverse TF (λ _ → 1 , unpack) u)
     ⟨ TraversableOKP.lawPHom {F} {TF} tokF {Batch X} {{ABatch}} {λ _ → ℕ} {{monoidApplicative {{sumMonoid}}}} fst (λ _ → 1 , unpack)
        (record { respPure = λ {X₁} x → refl
                ; resp-⍟  = λ f s → refl
                }) u ]=
   (traverse TF {λ _ → ℕ} {One {lzero}} {X}
     {{record { pure = λ {_} _ → 0; _<*>_ = λ {_} {_} → _+_ }}}
     (λ a → 1) u)
     =[ TraversableOKP.lawPCo {F} {TF} tokF
                              {G = id} {{AG = applicativeId}}
                              {H = λ _ → ℕ} {{AH = monoidApplicative}}
                              (λ _ → <>) (λ _ → 1) u ⟩
   (traverse TF {λ _ → ℕ} {One {lzero}} {One}
     {{record { pure = λ {_} _ → 0; _<*>_ = λ {_} {_} → _+_ }}}
     (λ a → 1) u)
     ∎

fromNormal :  ∀ {F}{{TF : Traversable F}} → TraversableOKP F →
              ∀ {X} → ⟦ normalT F ⟧ℕ X → F X
fromNormal {F} {{TF}} tokf {X} (sF , cF) with (coherence {F} {{TF}} {X} tokf sF)
fromNormal {F} {{TF}} tokf {X} (sF , cF) | q with batcher {F} {{TF}} sF {X}
fromNormal {F} {{TF}} tokf {X} (sF , cF) | q | n , csF = csF (subst (sym q) (λ u → Vec X u) cF)
-}

data Tree (N : Normal) : Set where
  ⟨_⟩ : ⟦ N ⟧ℕ (Tree N) → Tree N

NatT : Normal
NatT = Two / 0 ⟨?⟩ 1

zeroT : Tree NatT
zeroT = ⟨ tt , ⟨⟩ ⟩

sucT : Tree NatT → Tree NatT
sucT n = ⟨ ff , (n , ⟨⟩) ⟩

NatInd : ∀ {l} (P : Tree NatT → Set l) →
         P zeroT →
         ((n : Tree NatT) → P n → P (sucT n)) →
         (n : Tree NatT) → P n
NatInd P z s ⟨ tt , ⟨⟩ ⟩ = z
NatInd P z s ⟨ ff , (n , ⟨⟩) ⟩ = s n (NatInd P z s n)

All : ∀ {l X}(P : X → Set l) {n} → Vec X n → Set l
All P ⟨⟩ = One
All P (x , xs) = P x × All P xs

induction : ∀ (N : Normal) {l} (P : Tree N → Set l) →
            ((s : Shape N)(ts : Vec (Tree N) (size N s)) → All P ts → P  ⟨ s , ts ⟩) →
            (t : Tree N) → P t
induction N P p ⟨ s , ts ⟩ = p s ts (hyps ts) where
  hyps : ∀ {n} (ts : Vec (Tree N) n) → All P ts
  hyps ⟨⟩ = <>
  hyps (t , ts) = induction N P p t , hyps ts

eq? : (N : Normal)(sheq? : (s s` : Shape N) → Dec (s ≃ s`)) →
      (t t` : Tree N) → Dec (t ≃ t`)
eq? N sheq? t t' = {!   !}
