module Chapter2.LambdaCalculus where

open import Meta.Basics

-- Start with base types closed under function spaces.
data ⋆ : Set where
  ι : ⋆
  _▹_ : ⋆ → ⋆ → ⋆
infixl 5 _▹_

-- Add a dash of context
data Cx (X : Set) : Set where
  ε   : Cx X
  _,_ : Cx X → X → Cx X
infixl 4 _,_

-- And a skosh of de Bruijn indices.
data _∈_ (τ : ⋆) : Cx ⋆ → Set where
  zero : ∀ {Γ} → τ ∈ Γ , τ
  suc  : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ , σ
infix 3 _∈_

-- Mix well with syntax-directed typing judgements and serve immediately.
data _⊢_ (Γ : Cx ⋆) : ⋆ → Set where
  var : ∀ {τ}
      → τ ∈ Γ
      -------
      → Γ ⊢ τ
  lam : ∀ {σ τ}
      → Γ , σ ⊢ τ
      ------------
      → Γ ⊢ σ ▹ τ
  app : ∀ {σ τ}
      → Γ ⊢ σ ▹ τ → Γ ⊢ σ
      -------------------
      → Γ ⊢ τ
infix 2 _⊢_

-- Decode into Agda-isms.  This looks a hell of a lot like Augustsson and
-- Carlsson's first go at a decoder in "An exercise in dependent types: a well
-- typed interpreter."
⟦_⟧⋆ : ⋆ → Set
⟦ ι ⟧⋆ = ℕ -- "by way of being nontrivial"
⟦ σ ▹ τ ⟧⋆ = ⟦ σ ⟧⋆ → ⟦ τ ⟧⋆

-- Decode a context into an environment with a projection function.
⟦_⟧Cx : Cx ⋆ → (⋆ → Set) → Set
⟦ ε ⟧Cx V = One
⟦ (Γ , σ) ⟧Cx V = ⟦ Γ ⟧Cx V × V σ

-- Decode and project a term in context.
⟦_⟧∈ : ∀ {Γ τ V} → τ ∈ Γ → ⟦ Γ ⟧Cx V → V τ
⟦ zero ⟧∈ (γ , t) = t
⟦ suc i ⟧∈ (γ , s) = ⟦ i ⟧∈ γ

-- Finally, decode terms.
⟦_⟧⊢ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧Cx ⟦_⟧⋆ → ⟦ τ ⟧⋆
⟦ var i ⟧⊢ γ = ⟦ i ⟧∈ γ
⟦ lam t ⟧⊢ γ = λ s → ⟦ t ⟧⊢ (γ , s)
⟦ app f s ⟧⊢ γ = ⟦ f ⟧⊢ γ (⟦ s ⟧⊢ γ)

-- Ren: Simultaneous Renamings
-- Sub: Substitutions
Ren Sub : Cx ⋆ → Cx ⋆ → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ
Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

-- Extend a context with a list of variables.
_<><_ : ∀ { X } → Cx X → List X → Cx X
xz <>< ⟨⟩ = xz
xz <>< (x , xs) = xz , x <>< xs
infixl 3 _<><_

-- Shiftable Simultaneous Substitutions extend both contexts with the new list
-- of variables, then executes a Simultaneous substitution of the first into the
-- second.
Shub : Cx ⋆ → Cx ⋆ → Set
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

-- With this kit, pushing substitions under binders is trivial
_//_ : ∀ {Γ Δ}(θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
θ // var i = θ ⟨⟩ i -- Sub var is a context extension
θ // lam t = lam ((θ ∘ _,_ _) // t) -- Sub lam is lam of sub applied in the binding.
θ // app f s = app (θ // f) (θ // s) -- Sub app is sub down the binder and body.

-- Weakens both contexts in a renaming with σ.
wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
wkr r zero = zero -- Weakening a renaming in the empty context does nothing.
wkr r (suc n) = suc (r n) -- Else iteratively weaken the renaming with the variable.

-- So a renaming can be made into a shiftable substitution simply by iteratively
-- weakening the renaming.
ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren r ⟨⟩ = var ∘ r -- Shub for the empty renaming is just the names we already know.
ren r (_ , Ξ) = ren (wkr r) Ξ -- Else Shub by weakening the context.

-- So a substitution can be made into a shiftable substitution simply by
-- iteratively weakening the substitution.
sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub s ⟨⟩ = s
sub s (_ , Ξ) = sub (wks s) Ξ
  where
    -- Weaks both contexts in a substitution with σ.
    wks : ∀ {Γ Δ σ} → Sub Γ Δ → Sub (Γ , σ) (Δ , σ)
    wks s zero = var zero -- Weakening a substitution in the empty context does nothing.
    wks s (suc n) = ren suc // s n -- Else iteratively weaken the substitution.

-- "A renaming that shifts past any context extension."
weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
weak ⟨⟩ i = i -- Shift once in the empty context.
weak (_ , Ξ) i = weak Ξ (suc i) -- Shift 1 + the context

lambda' : ∀ {Γ σ τ} → ((∀ {Ξ} → Γ , σ <>< Ξ ⊢ σ) → Γ , σ ⊢ τ) → Γ ⊢ σ ▹ τ
lambda' f = lam (f λ {Ξ} → var (weak Ξ zero))

-- "... Constructor-based unification is insufficient to solve for the prefix of
-- a context, given a common suffix.
--
-- By contrast, solving for a suffix is easy when the prefix is just a value: it
-- requires only the stripping off of matching constructors. So, we can cajole
-- Agda into solving the problem by working with its reversal, via the ‘chips’
-- operator:"
_<>>_ : ∀ {X} → Cx X → List X → List X
ε <>> ys = ys
(xz , x) <>> ys = xz <>> (x , ys)

open import Agda.Primitive

lambda : ∀ {Γ σ τ} → ((∀ {Δ Ξ} {{_ : Δ <>> ⟨⟩ ≃ Γ <>> (σ , Ξ)}} → Δ ⊢ σ) → Γ , σ ⊢ τ) → Γ ⊢ σ ▹ τ
lambda {Γ} f = lam ((f λ {Δ Ξ}{{q}} → subst (lem Δ Γ (_ , Ξ) q) (λ Γ → Γ ⊢ _) (var (weak Ξ zero))))
  where
    {- This is Conor's.  He wasn't kidding about the ugly. -}
    sucI : (a b : ℕ) → (_≃_ {lzero}{ℕ} (suc a) (suc b)) → a ≃ b
    sucI .b b refl = refl

    grr : (x y : ℕ) → suc x + y ≃ x + suc y
    grr zero y = refl
    grr (suc x) y rewrite grr x y = refl

    _+a_ : ℕ → ℕ → ℕ
    zero +a y = y
    suc x +a y = x +a suc y

    noc' : (x y : ℕ) → suc (x + y) ≃ y → {A : Set} → A
    noc' x zero ()
    noc' x (suc y) q = noc' x y
       (suc (x + y) =[ grr x y ⟩ x + suc y =[ sucI _ _ q ⟩ y ∎)

    noc : (x k y : ℕ) → x +a (suc k + y) ≃ y → {A : Set} → A
    noc zero k y q = noc' k y q
    noc (suc x) k y q = noc x (suc k) y q

    len : ∀ {X} → Cx X → ℕ
    len ε = zero
    len (xz , x) = suc (len xz)

    lenlem : ∀ {X}(xz : Cx X)(xs : List X) → length (xz <>> xs) ≃ len xz +a length xs
    lenlem ε xs = refl
    lenlem (xz , x) xs = lenlem xz (x , xs)

    lem0 : ∀ {X}(xz yz : Cx X)(xs ys : List X) → length xs ≃ length ys → xz <>> xs ≃ yz <>> ys → (xz ≃ yz) × (xs ≃ ys)
    lem0 ε ε xs ys q q' = refl , q'
    lem0 ε (yz , x) .(yz <>> (x , ys)) ys q refl rewrite lenlem yz (x , ys) = noc (len yz) zero (length ys) q
    lem0 (xz , x) ε xs .(xz <>> (x , xs)) q refl rewrite lenlem xz (x , xs) = noc (len xz) zero (length xs) (_ ⟨ q ]= _ ∎)
    lem0 (xz , x) (yz , y) xs ys q q' with lem0 xz yz (x , xs) (y , ys) (cong suc q) q'
    lem0 (.yz , .y) (yz , y) .ys ys q q' | refl , refl = refl , refl

    lem : ∀ {X} (Δ Γ : Cx X) Ξ → Δ <>> ⟨⟩ ≃ Γ <>> Ξ → Γ <>< Ξ ≃ Δ
    lem Δ Γ ⟨⟩ q = Γ
                 ⟨ fst (lem0 Δ Γ ⟨⟩ ⟨⟩ refl q) ]= Δ
                   ∎
    lem Δ Γ (x , Ξ) q = lem Δ (Γ , x) Ξ q

{-
myTest : ε ⊢ ι ▹ ι
myTest = lambda λ x → x

myTest2 : ε ⊢ (ι ▹ ι) ▹ (ι ▹ ι)
myTest2 = lambda λ f → lambda λ x → app f (app f x)
-}

-- "The right-nested spine representation of β-normal η-long forms.
-- In other words, Γ ⊨ τ is a normal form in τ and Γ ⊨* τ is a spine for τ
-- that'll give you a term ι if you ask nicely.
mutual
  -- Γ ⊨ τ is the type of normal forms in τ
  data _⊨_ (Γ : Cx ⋆) : ⋆ → Set where
    lam : ∀ {σ τ} → Γ , σ ⊨ τ → Γ ⊨ σ ▹ τ
    _$_ : ∀ {τ} → τ ∈ Γ → Γ ⊨* τ → Γ ⊨ ι

  -- Γ ⊨* τ is the type of spines for τ delivering ι.
  data _⊨*_ (Γ : Cx ⋆) : ⋆ → Set where
    -- Just deliver ι
    ⟨⟩ : Γ ⊨* ι
    -- ι comes with a sequence of destructors applied to it that have to
    -- be normalized away.
    _,_ : ∀ {σ τ} → Γ ⊨ σ → Γ ⊨* τ → Γ ⊨* σ ▹ τ
infix 3 _⊨_ _⊨*_
infix 3 _$_

-- Removes the term x from the context.
_-×_ : ∀ (Γ : Cx ⋆) {τ} (x : τ ∈ Γ) → Cx ⋆
ε -× ()
(Γ , _) -× zero = Γ
(Γ , sg) -× suc x = (Γ -× x) , sg
infixl 4 _-×_

-- Embeds a smaller context into a larger one through a
_≠_ : ∀ {Γ σ} (x : σ ∈ Γ) → Ren (Γ -× x) Γ
zero ≠ y = suc y
suc x ≠ zero = zero
suc x ≠ suc y = suc (x ≠ y)

{-
⟨_|⟶_⟩_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ -× x ⊨ σ → Γ ⊨ τ → Γ -× x ⊨ τ
⟨ x |⟶ s ⟩ lam t = lam (⟨ suc x |⟶ {!   !} ⟩ t)
⟨ x |⟶ s ⟩ (x₁ $ x₂) = {!   !}
-}

-- Boolean equality is insufficient to identify whether a term is a suitable
-- spine for the expression - we need to know its representation in Γ -× x.
data Veq? {Γ σ}(x : σ ∈ Γ) : ∀ {τ} → τ ∈ Γ → Set where
  same  :                         Veq? x x
  diff  : ∀ {τ}(y : τ ∈ Γ -× x) → Veq? x (x ≠ y)

-- Show that every |y| is discriminable with respect to a given |x|.

veq? : ∀ {Γ σ τ}(x : σ ∈ Γ)(y : τ ∈ Γ) → Veq? x y
veq? zero zero      = same
veq? zero (suc y)   = diff y
veq? (suc x) zero  = diff zero
veq? (suc x) (suc y) with  veq? x y
veq? (suc x) (suc .x) | same = same
veq? (suc x) (suc .(x ≠ y)) | diff y = diff (suc y)

-- Show how to propagate a renaming through a normal form.
mutual
  -- Renaming for normal forms.
  renNm : ∀ {Γ Δ τ} → Ren Γ Δ → Γ ⊨ τ → Δ ⊨ τ
  -- Push the renaming under the binder and push the renaming through the body
  -- of the binder by iteratively weakening the context at each level with the
  -- renaming.
  renNm ρ (lam n) = lam (renNm (wkr ρ) n)
  -- Rename the bound variable and push the renaming through the spine of the
  -- right side of the application.
  renNm ρ (f $ x) = ρ f $ (renSp ρ x)

  -- Renaming with spines.  Maps a normal form renaming over each destructor.
  renSp : ∀ {Γ Δ τ} → Ren Γ Δ → Γ ⊨* τ → Δ ⊨* τ
  renSp ρ ⟨⟩ = ⟨⟩
  renSp ρ (x , ss) = renNm ρ x , renSp ρ ss

-- Implement hereditary substitution for normal forms and spines, defined
-- mutually with application of a normal form to a spine, performing β-reduction.
mutual
  -- Substitution for normal forms.
  ⟨_↦_⟩_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ -× x ⊨ σ → Γ ⊨ τ → Γ -× x ⊨ τ
  -- Push the substitution under the binder and recurse.
  ⟨ x ↦ s ⟩ lam t = lam (⟨ suc x ↦ renNm (_≠_ zero) s ⟩ t)
  -- Are you ready for a substitution?
  ⟨ x ↦ s ⟩ x₁ $ x₂ with veq? x x₁
  -- Yep!  Sub in s in the binder and recurse into the spine to keep renaming.
  ⟨ x ↦ s ⟩ .x $ xs | same = s $$ (⟨ x ↦ s ⟩* xs)
  -- Nope!  Don't sub, but recurse into the spine to try again.
  ⟨ x ↦ s ⟩ .(x ≠ y) $ xs | diff y = y $ (⟨ x ↦ s ⟩* xs)

  -- Substitution for spines.  As before, map normal-form substitution down the
  -- spine.
  ⟨_↦_⟩*_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ -× x ⊨ σ → Γ ⊨* τ → Γ -× x ⊨* τ
  ⟨ x ↦ s ⟩* ⟨⟩ = ⟨⟩
  ⟨ x ↦ s ⟩* (t , ts) = (⟨ x ↦ s ⟩ t) , (⟨ x ↦ s ⟩* ts)

  -- Evaluation of the destructors in a spine
  _$$_ : ∀ {Γ τ} → Γ ⊨ τ → Γ ⊨* τ → Γ ⊨ ι
  -- Yield ι
  f $$ ⟨⟩ = f
  -- Substitute the argument into the body of the function.
  lam f $$ (s , ss) = (⟨ zero ↦ s ⟩ f) $$ ss
infix 3 _$$_
infix 2 ⟨_↦_⟩_

-- Delivers a variable x in η-long form.
-- Naturally, this is Conor's.  I can't really think of a better way to do this.
η : ∀ {Γ σ}(x : σ ∈ Γ) τ → (∀ {Δ} → Ren Γ Δ → Δ ⊨* τ → Δ ⊨* σ) → Γ ⊨ τ
η x ι f = x $ f id ⟨⟩
η x (σ ▹ τ) f = lam (η (suc x) τ λ ρ ss → f (ρ ∘ suc) ((η (ρ zero) σ (λ _ → id)) , ss))

-- The usual normalization, but η-long
normalize : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normalize (var x) = η x _ λ _ → id -- Do nothing
normalize (lam t) = lam (normalize t) -- Normalize under the binder
normalize (app f s) with normalize f | normalize s -- Normalize both sides
normalize (app f s) |    lam t       | s2 = ⟨ zero ↦ s2 ⟩ t -- Hereditary sub into
                                          -- nothing to apply, then normalize under the binder

{-
try₁ : ε ⊨ ((ι ▹ ι) ▹ (ι ▹ ι)) ▹ (ι ▹ ι) ▹ (ι ▹ ι)
try₁ = normalize (lambda id)

church₂ : ∀ {τ} → ε ⊢ (τ ▹ τ) ▹ τ ▹ τ
church₂ = lambda λ f → lambda λ x → app f (app f x)

try₂ : ε ⊨ (ι ▹ ι) ▹ (ι ▹ ι)
try₂ = normalize (app (app church₂ church₂) church₂)
-}

-- Creative normalization involves:
data Stop (Γ : Cx ⋆) (τ : ⋆) : Set where
  var : τ ∈ Γ → Stop Γ τ -- non-η-long forms that don't understand app
  _$_ : ∀ {σ} → Stop Γ (σ ▹ τ) → Γ ⊨ σ → Stop Γ τ -- and η-long forms that understand app

-- Lift a renaming into some creative normalization.
renSt : ∀ {Γ Δ τ} → Ren Γ Δ → Stop Γ τ → Stop Δ τ
renSt r (var x) = var (r x)
renSt r (u $ s) = renSt r u $ renNm r s

-- Applying a Stop term to a spine yields a normal form.
stopSp : ∀ {Γ τ} → Stop Γ τ → Γ ⊨* τ → Γ ⊨ ι
stopSp (var x) ss = x $ ss
stopSp (u $ x) ss = stopSp u (x , ss)

-- Look, semantics in a context.  Looks positively Kripkean.
mutual
  -- Values either Go or Stop
  Val : Cx ⋆ → ⋆ → Set
  Val Γ τ = Go Γ τ ⊎ Stop Γ τ

  Go : Cx ⋆ → ⋆ → Set
  Go Γ ι = Zero
  Go Γ (σ ▹ τ) = ∀ {Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ

-- Show that values admit renaming.  Extend renaming to environments storing
-- values.  Construct the identity environment mapping each variable to itself.
renVal : ∀ {Γ Δ} τ → Ren Γ Δ → Val Γ τ → Val Δ τ
renVal τ r (ff , u) = ff , renSt r u
renVal ι r (tt , ())
renVal (σ ▹ τ) r (tt , f) = tt , (λ r' s → f (r' ∘ r) s)

renVals : ∀ Θ {Γ Δ} → Ren Γ Δ → ⟦ Θ ⟧Cx (Val Γ) → ⟦ Θ ⟧Cx (Val Δ)
renVals ε r _ = <>
renVals (Θ , σ) r (θ , τ) = (renVals Θ r θ) , renVal σ r τ

idEnv : ∀ Γ → ⟦ Γ ⟧Cx (Val Γ)
idEnv ε = <>
idEnv (Γ , σ) = renVals Γ suc (idEnv Γ) , (ff , var zero)

mutual
  apply : ∀ {Γ σ τ} → Val Γ (σ ▹ τ) → Val Γ σ → Val Γ τ
  apply (tt , f) s = f id s
  apply (ff , u) s = ff , (u $ quo _ s)

  quo : ∀ {Γ} τ → Val Γ τ → Γ ⊨ τ
  quo ι (tt , ())
  quo ι (ff , u) = stopSp u ⟨⟩
  quo (σ ▹ τ) v = lam (quo τ (apply (renVal _ suc v) (ff , var zero)))

-- Look, Kripe again.
eval : ∀ {Γ Δ τ} → Γ ⊢ τ → ⟦ Γ ⟧Cx (Val Δ) → Val Δ τ
eval (var x) γ = ⟦ x ⟧∈ γ
eval {Γ}{_}{_} (lam t) γ = tt , λ r s → eval t (renVals Γ r γ , s)
eval (app f s) γ = apply (eval f γ) (eval s γ)

-- "With all the pieces in place, we get:"
normByEval : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normByEval {Γ}{τ} t = quo τ (eval t (idEnv Γ))

{-
zero : Γ ⊢ ι
suc : Γ ⊢ ι → Γ ⊢ ι
rec : ∀ {τ} → Γ ⊢ τ → Γ ⊢ (ι ▹ τ ▹ τ) → Γ ⊢ ι → Γ ⊢ τ
-}
