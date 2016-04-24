module Meta.Data.Vector where

open import Meta.Basics
open import Meta.Data.EndoFunctor
open import Meta.Control.Applicative
open import Meta.Control.Monad
open import Meta.Data.Fin

data Vec (X : Set) : ℕ → Set where
  ⟨⟩ : Vec X zero
  _,_ : {n : ℕ} → X → Vec X n → Vec X (suc n)

head : ∀ {n X} → Vec X (suc n) → X
head (x , xs) = x

tail : ∀ {n X} → Vec X (suc n) → Vec X n
tail (x , xs) = xs

{-
zip : forall {n S T} → Vec S n → Vec T n → Vec (S × T) n
zip ⟨⟩ ⟨⟩ = ⟨⟩
zip (x , xs) (y , ys) = (x , y) , zip xs ys
-}

vec : forall {n X} → X → Vec X n
vec {zero} x = ⟨⟩
vec {suc n} x = x , vec x

vapp : ∀ {n S T} → Vec (S → T) n → Vec S n → Vec T n
vapp ⟨⟩ ⟨⟩ = ⟨⟩
vapp (x , fs) (x₁ , ss) = x x₁ , vapp fs ss

vmap : ∀ {n S T} → (S → T) → Vec S n → Vec T n
vmap f xs = vapp (vec f) xs
{-
vmap f ⟨⟩ = ⟨⟩
vmap f (x , xs) = f x , vmap f xs
-}

zipV : ∀ {n S T} → Vec S n → Vec T n → Vec (S × T) n
zipV ss ts = vapp (vapp (vec _,_) ss) ts

zipWithV : ∀ {n S T U} → (S → T → U) → Vec S n → Vec T n → Vec U n
zipWithV f ⟨⟩ ⟨⟩ = ⟨⟩
zipWithV f (a , as) (b , bs) = f a b , zipWithV f as bs

_++_ : ∀ {m n X} → Vec X m → Vec X n → Vec X (m + n)
⟨⟩ ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)

vfoldl : ∀ {n S}{T : Set} → (T → S → T) → T → Vec S n → T
vfoldl f i ⟨⟩ = i
vfoldl f i (x , xs) = vfoldl f (f i x) xs

chop : forall {X} m {n} → Vec X (m + n) → (Vec X m) × (Vec X n)
chop zero xs = ⟨⟩ , xs
chop (suc m) (x , xs) with chop m xs
... | ys , zs = (x , ys) , zs

vreplicate : ∀ {X} → (n : ℕ) → (x : X) → Vec X n
vreplicate zero     x = ⟨⟩
vreplicate (suc k) x = x , vreplicate k x

proj : ∀ {n X} → Vec X n → Fin n → X
proj ⟨⟩ ()
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i

tabulate : ∀ {n X} → (Fin n → X) → Vec X n
tabulate {zero} f = ⟨⟩
tabulate {suc n} f = f zero , tabulate (λ _ → f zero)

concat : ∀ {n X} → Vec (Vec X n) n → Vec X n
concat ⟨⟩             = ⟨⟩
concat ((x , xs) , xss) = x , concat (vmap tail xss)

instance
  monadVec : ∀ {n} → Monad λ X → Vec X n
  monadVec = record { return = vec; _>>=_ = λ m f → concat (vmap f m) }

  applicativeVec : ∀ {n} → Applicative λ X → Vec X n
  applicativeVec = record { pure = vec; _⍟_ = vapp }

  endoFunctorVec : ∀ {n} → EndoFunctor λ X → Vec X n
  endoFunctorVec = record { map = vmap }

  vecEndoFunctorOKP : ∀ {n} → EndoFunctorOKP (λ X → Vec X n)
  vecEndoFunctorOKP = record { endoFunctorId = vecId; endoFunctorCo = λ f g → vecComp f g }
    where
      vecId : ∀ {n X} → (x : Vec X n) → vapp (vec id) x ≃ x
      vecId ⟨⟩ = refl
      vecId (x , xs) rewrite vecId xs = refl

      vecComp : ∀ {n R S T} → (f : S → T)(g : R → S) → (x : Vec R n) → (map f ∘ map g) x ≃ map (f ∘ g) x
      vecComp f g ⟨⟩ = refl
      vecComp f g (x , xs) rewrite vecComp f g xs = refl

allFin : ∀ n → Vec (Fin n) n
allFin zero    = ⟨⟩
allFin (suc n) = zero , map suc (allFin n)
