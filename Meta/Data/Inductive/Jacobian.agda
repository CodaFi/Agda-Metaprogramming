module Meta.Data.Inductive.Jacobian where

open import Meta.Basics
open import Meta.Data.Functor.Container.Indexed
open import Meta.Data.Inductive.ITree
open import Meta.Data.Functor.Container
open import Meta.Data.Inductive.W

Jac : ∀ {I J} -> I ▷ J -> I ▷ (J × I)
Jac (S ◃ P $ r)
  =   (\ { (j , i) -> Σ (S j) λ s → r j s ⁻¹ i })
  ◃  (\ { (j , .(r j s p)) (s , from p) → P j s ─ p })
  $   (\ { (j , .(r j s p)) (s , from p) (p' , _) → r j s p' })
  
plugIx : ∀ {I J} (C : I ▷ J) → ((j : J)(s : Shlx C j)(p p₁ : Polx C j s) → Dec (p ≃ p₁)) →
         ∀ {i j X} → ⟦ Jac C ⟧ᵢ X (j , i) → X i → ⟦ C ⟧ᵢ X j
plugIx C eq? {X = X} ((s , from p) , k) x = {!!}

Zipper : ∀ {I} → I ▷ I → (I × I) ▷ (I × I)
Zipper {I} C = (λ { (fst , snd) → (fst ≃ snd) ⊎ Σ I λ ip → ⟦ Jac C ⟧ᵢ (ITree C) (ip , snd) })
         ◃ (λ { _ (tt , _) → Zero ; _ (ff , _) → One })
         $ (λ { _ (tt , snd) () ; (fst , snd) (ff , (fst₁ , _)) _ → fst , fst₁ })

zipOut : ∀ {I} (C : I ▷ I) {ir ih} →
         ((i : I)(s : Shlx C i)(p p₁ : Polx C i s) → Dec (p ≃ p₁)) →
         ITree (Zipper C) (ir , ih) → ITree C ih → ITree C ir
zipOut C eq? ⟨ (tt , refl) , _ ⟩ t = t
zipOut C eq? ⟨ (ff , (_ , c)) , cz ⟩ t = zipOut C eq? (cz <>) ⟨ plugIx C eq? c t ⟩

▽ : {I : Set} → Desc I → I → Desc I
▽ (var x) h = κ (x ≃ h)
▽ (σ A D) h = σ A λ a → ▽ (D a) h
▽ (π A D) h = σ A λ a → ▽ (D a) h ×D π (A ─ a) λ { (a₁ , _) → D a₁ }
▽ (D ×D E) h = σ Two ((▽ D h ×D E) ⟨?⟩ (D ×D ▽ E h))
▽ (κ x) h = κ Zero




