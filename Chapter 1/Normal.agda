module Normal where

open import Basics
open import Function using (const)

open import Vector
open import Applicative
open import Traversable
open import Monoid

record Normal : Set1 where
  constructor _/_
  field
    Shape : Set
    size : Shape → ℕ
  ⟦_⟧ℕ : Set → Set
  ⟦_⟧ℕ X = Sg Shape λ s → Vec X (size s)
open Normal public
infixr 0 _/_

VecN : ℕ → Normal
VecN n = One / const n

ListN : Normal
ListN = ℕ / id

Kℕ : Set → Normal
Kℕ A = A / const 0

IKℕ : Normal
IKℕ = VecN 1

_+N_ : Normal -> Normal -> Normal
(ShF / szF) +N (ShG / szG) = (ShF ⊎ ShG) / vv szF ⟨?⟩ szG

_×N_ : Normal -> Normal -> Normal
(ShF / szF) ×N (ShG / szG) = (ShF × ShG) / vv λ f g → szF f + szG g

nInj : ∀ { X } (F G : Normal) → ⟦ F ⟧ℕ X ⊎ ⟦ G ⟧ℕ X → ⟦ F +N G ⟧ℕ X
nInj F G (tt , ShF , xs) = (tt , ShF) , xs
nInj F G (ff , ShG , xs) = (ff , ShG) , xs

data _^-1_ { S T : Set }(f : S → T) : T → Set where
  from : (s : S) → f ^-1 f s

nCase : ∀ { X } F G (s :  ⟦ F +N G ⟧ℕ X) → nInj F G ^-1 s
nCase F G ((tt , ShF) , xs) = from (tt , ShF , xs)
nCase F G ((ff , ShG) , xs) = from (ff , ShG , xs)

nOut : ∀ { X }(F G : Normal) → ⟦ F +N G ⟧ℕ X → ⟦ F ⟧ℕ X ⊎ ⟦ G ⟧ℕ X
nOut F G xs' with nCase F G xs'
nOut F G . (nInj F G xs) | from xs = xs

nPair : ∀ { X }(F G : Normal) →  ⟦ F ⟧ℕ X × ⟦ G ⟧ℕ X → ⟦ F ×N G ⟧ℕ X
nPair F G ((ShFx , fs) , (ShGx , gs)) = (ShFx , ShGx) , fs ++ gs

concatSurjectivity : forall {m n : ℕ} {X} -> (x : Vec X (m + n)) -> (vv \ (u : Vec X m) (v : Vec X n) -> u ++ v)  ^-1 x
concatSurjectivity {zero} v = from (? , v)
concatSurjectivity {suc m} (x , v) with concatSurjectivity {m} v
concatSurjectivity {suc m} (x , .(u ++ w)) | from (u , w) = from ((x , u) , w)


unAppend : ∀ m n {X} -> (xsys : Vec X (m + n)) -> (vv _++_ {m}{n}) ^-1 xsys
unAppend zero n ys = from (⟨⟩ , ys)
unAppend (suc m) n (x , xsys) with unAppend m n xsys
unAppend (suc m) n (x , .(xs ++ ys)) | from (xs , ys) = from ((x , xs) , ys)

listNMonoid : {X : Set} → Monoid (⟦ ListN ⟧ℕ X)
listNMonoid = record
  { ε = (zero , ⟨⟩)
  ; _•_ = _++N_
  } where
    _++N_ : {X : Set} -> ⟦ ListN ⟧ℕ X -> ⟦ ListN ⟧ℕ X -> ⟦ ListN ⟧ℕ X
    (n , xs) ++N (m , ys) = (n + m , xs ++ ys)

{-
listNMonoidOK : {X : Set} → MonoidOK (⟦ ListN ⟧ℕ X) {{listNMonoid}}
listNMonoidOK {X} = record
  { absorbL = λ _ → refl
  ; absorbR = vv ++<>
  ; assoc = λ _ _ _ → refl
  } where
    ++<> : {M : Monoid (⟦ ListN ⟧ℕ X)} → (n : ℕ) (xs : Vec X n) → (n , xs) • (zero , ⟨⟩) ≃ (n , xs)
    ++<> zero ⟨⟩ = refl
    ++<> (suc n) (x , xs) = cong (vv λ m ys → suc m , x , ys) (++<> n xs)
-}

normalTraversable : (F : Normal) -> Traversable ⟦ F ⟧ℕ
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) ⍟ traverse {{traversableVec}} f xs }

_◦N_ : Normal → Normal → Normal
F ◦N (ShG / szG) =  ⟦ F ⟧ℕ ShG / crush {{normalTraversable F}}{{sumMonoid}} szG

sizeT : ∀ {F}{{TF : Traversable F}}{X} → F X → ℕ
sizeT {F}{{TF}} = crush {{TF}}{{sumMonoid}} (λ _ → 1)

normalT : ∀ F {{TF : Traversable F}} → Normal
normalT F = F One / sizeT

shapeT : ∀ {F}{{TF : Traversable F}}{X} → F X → F One
shapeT = {!!}
-- shapeT {F}{{TF}}{{AG}} xs = traverse {{TF}}{F}{{AG}} ?

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

toNormal : ∀ {F}{{TF : Traversable F}}{X} → F X → ⟦ normalT F ⟧ℕ X
toNormal fx = {!!}

_⊗_ : Normal → Normal → Normal
(ShF / szF) ⊗ (ShG / szG) = (ShF × ShG) / λ s → szF (fst s) * szG (snd s)

fromMatrix : {m n : ℕ} {X : Set} -> Vec (Vec X n) m -> Vec X (m * n)
fromMatrix ⟨⟩ = ⟨⟩
fromMatrix (v , vs) = {!!}

unfromMatrix : (m n : ℕ) {X : Set} → (elts : Vec X (n * m)) → fromMatrix {n}{m}^-1 elts
unfromMatrix _ _ _ = {!!}
{-
unfromMatrix m zero ⟨⟩ = from ⟨⟩
unfromMatrix m (suc n) elts with unAppend m (m * n) elts
unfromMatrix m (suc n) .(col ++ rest) | from (col , rest) with unfromMatrix m n rest
unfromMatrix m (suc n) .(col ++ fromMatrix cols) | from (col , .(fromMatrix cols)) | from cols = from (col , cols)
-}

toMatrix : {m n : ℕ} {X : Set} → Vec X (n * m) → Vec (Vec X m) n
toMatrix {m} {n} elts with unfromMatrix m n elts
toMatrix .(fromMatrix m) | from m = m

swap : (F G : Normal) → (F ⊗ G) ⟶N (G ⊗ F)
swap F G (ShF , ShG) = ((ShG , ShF) , fromMatrix {size G ShG} {size F ShF} (transpose (toMatrix (tabulate id))))

drop : (F G : Normal) → (F ⊗ G) ⟶N (F ◦N G)
drop F G (ShF , ShG) = (ShF , (vec ShG)) , {!!}
 where
  k : {n m : ℕ} -> n ≃ m -> Vec (Fin m) n
  k {n} {.n} refl = tabulate id
  
fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ℕ X}{{listNMonoid}}{ℕ}{{sumMonoid}} fst
fstHom = record
  { respε = refl
  ; resp• = λ _ _ → refl
  }

Batch : Set -> Set -> Set
Batch X Y = Sg ℕ \ n -> Vec X n -> Y

ABatch : {X : Set} -> Applicative  (Batch X)
ABatch {X} =
  record {
    pure = λ y → 0 , (λ x → y);
    _⍟_ = app
  } where
    app : {S T : Set} -> Batch X (S -> T) -> Batch X S -> Batch X T
    app (n , vs) (m , us) = (n + m) , (λ ws → splitAndApply ws) where
      splitAndApply : (ws : Vec _ (n + m)) -> _
      splitAndApply ws with concatSurjectivity {n} ws
      splitAndApply .(vi ++ ui) | from (vi , ui) = (vs vi) (us ui)

unpack : ∀ {X} -> Vec X 1 -> X
unpack (x , _) = x

batcher : forall {F} {{TF : Traversable F}} -> F One -> forall {X} -> Batch X (F X)
batcher {F} {{TF}} sF {X} = traverse {F} {{TF}} {Batch X} {{ABatch}} (λ _ → 1 , unpack) sF 

open import Level

coherence : ∀ {F} {{TF : Traversable F}} {X} -> TraversableOKP F 
            → (sF : F One) →
               fst (batcher {F} {{TF}} sF {X}) ≃
               traverse {F} {{TF}} {λ _ → ℕ} {One} {One} {{monoidApplicative}} (λ _ → 1) sF
coherence {F} {{TF}} {X} tokF u = 
   fst (traverse TF (λ _ → 1 , unpack) u) 
     ⟨ TraversableOKP.lawPHom {F} {TF} tokF {Batch X} {{ABatch}} {λ _ → ℕ} {{monoidApplicative}} fst (λ _ → 1 , unpack) 
        (record { respPure = λ {X₁} x → refl
                ; respApp  = λ f s → refl
                }) u ]= 
   (traverse TF {λ _ → ℕ} {One {Level.zero}} {X}
     {{record { pure = λ {_} _ → 0; _<*>_ = λ {_} {_} → _+_ }}}
     (λ a → 1) u)
     =[ TraversableOKP.lawPCo {F} {TF} tokF 
                              {G = id} {{AG = applicativeId}} 
                              {H = λ _ → ℕ} {{AH = monoidApplicative}} 
                              (λ _ → <>) (λ _ → 1) u ⟩
   (traverse TF {λ _ → ℕ} {One {Level.zero}} {One}
     {{record { pure = λ {_} _ → 0; _<*>_ = λ {_} {_} → _+_ }}}
     (λ a → 1) u)
     ∎
     
fromNormal :  ∀ {F}{{TF : Traversable F}} -> TraversableOKP F ->
              ∀ {X} -> ⟦ normalT F ⟧ℕ X -> F X
fromNormal {F} {{TF}} tokf {X} (sF , cF) with (coherence {F} {{TF}} {X} tokf sF) 
fromNormal {F} {{TF}} tokf {X} (sF , cF) | q with batcher {F} {{TF}} sF {X} 
fromNormal {F} {{TF}} tokf {X} (sF , cF) | q | n , csF = csF (subst (symmetry q) (λ u → Vec X u) cF)

data Tree (N : Normal) : Set where
  ⟨_⟩ : ⟦ N ⟧ℕ (Tree N) → Tree N

NatT : Normal
NatT = Two / 0 ⟨?⟩ 1

zeroT : Tree NatT
zeroT = ⟨ tt , ⟨⟩ ⟩

sucT : Tree NatT → Tree NatT
sucT n = ⟨ ff , n , ⟨⟩ ⟩

NatInd : ∀ {l} (P : Tree NatT → Set l) →
         P zeroT →
         ((n : Tree NatT) → P n → P (sucT n)) →
         (n : Tree NatT) → P n
NatInd P z s ⟨ tt , ⟨⟩ ⟩ = z
NatInd P z s ⟨ ff , n , ⟨⟩ ⟩ = s n (NatInd P z s n)

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
eq? N sheq? t t' = tt , {!!}
