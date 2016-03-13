module Chapter4.Jacobian where

open import Meta.Basics
open import Chapter4.IndexedContainers
open import Chapter4.ITree
open import Meta.Data.Inductive.W
open import Meta.Data.Functor.Container

-- The derivative of I ▷ J is I ▷ (J × I) where a (j, i) derivative is a
-- structure of index j with a hole of index i.
-- Shapes: (i, j) derivatives
-- Positions: the hole at index i
-- Elements:
Jac : ∀ {I J} -> I ▷ J -> I ▷ (J × I)
Jac (S ◃ P $ r)
  =   (\ { (j , i) -> Σ (S j) λ s → r j s ⁻¹ i })
  ◃  (\ { (j , .(r j s p)) (s , from p) → P j s ─ p })
  $   (\ { (j , .(r j s p)) (s , from p) (p' , _) → r j s p' })

plugIx : ∀ {I J} (C : I ▷ J) → ((j : J)(s : ShIx C j)(p p₁ : PoIx C j s) → Dec (p ≃ p₁)) →
         ∀ {i j X} → ⟦ Jac C ⟧ᵢ X (j , i) → X i → ⟦ C ⟧ᵢ X j
plugIx C eq? {X = X} ((s , from p) , k) x = s , help where
  help : (p : PoIx C _ s) -> X (riIx C _ s p)
  help p' with eq? _ s p' p
  help .p | tt , refl = x
  help p' | ff , np = k (p' , np)

-- 4.12 (the Zipper) For a given C : I ▷ I, construct the indexed container
-- Zipper C : (I × I) ▷ (I × I) such that ITree (Zipper C) (ir, sh) represents
-- a one ih-hole context in a ITree C ir, represented as a sequence of
-- hole-to-root layers.
Zipper : ∀ {I} → I ▷ I → (I × I) ▷ (I × I)
Zipper {I} C = (λ { (fst , snd) → (fst ≃ snd) ⊎ Σ I λ ip → ⟦ Jac C ⟧ᵢ (ITree C) (ip , snd) })
         ◃ (λ { _ (tt , _) → Zero ; _ (ff , _) → One })
         $ (λ { _ (tt , snd) () ; (fst , snd) (ff , (fst₁ , _)) _ → fst , fst₁ })

-- Check that you can zipper all the way out to the root.
zipOut : ∀ {I} (C : I ▷ I) {ir ih} →
         ((i : I)(s : ShIx C i)(p p₁ : PoIx C i s) → Dec (p ≃ p₁)) →
         ITree (Zipper C) (ir , ih) → ITree C ih → ITree C ir
zipOut C eq? ⟨ (tt , refl) , _ ⟩ t = t
zipOut C eq? ⟨ (ff , (_ , c)) , cz ⟩ t = zipOut C eq? (cz <>) ⟨ plugIx C eq? c t ⟩

-- 4.13 (differentiating Desc) The notion corresponding to Jac for descriptions
-- is ▽, computing a 'vector' of partial derivatives.  Define it symbolically.
▽ : {I : Set} → Desc I → I → Desc I
▽ (var x) h = κ (x ≃ h) -- ▽ X is a constant (⊤)
▽ (σ A D) h = σ A λ a → ▽ (D a) h -- ▽ (A + D) is a vector of derivatives indexed by A.
▽ (π A D) h = σ A λ a → ▽ (D a) h ×D π (A ─ a) λ { (a₁ , _) → D a₁ } -- ▽ (A × D) is a matrix of derivatives yielding column vectors indexed by A
▽ (D ×D E) h = σ Two ((▽ D h ×D E) ⟨?⟩ (D ×D ▽ E h)) -- The product rule
▽ (κ x) h = κ Zero -- The derivative of a constant is 0
