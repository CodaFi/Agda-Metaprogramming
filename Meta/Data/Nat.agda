module Meta.Data.Nat where

open import Meta.Basics
open import Meta.Data.Monoid

+-suc : ∀ x y → x + suc y ≃ suc (x + y)
+-suc zero y = refl
+-suc (suc x) y rewrite +-suc x y = refl

+-commute : ∀ x y → x + y ≃ y + x
+-commute zero y rewrite (MonoidOK.absorbR natMonoidOK y) = refl
+-commute (suc x) y rewrite +-suc y x | +-commute x y = refl

_*zero : ∀ x → x * zero ≃ zero
zero *zero = refl
suc n *zero rewrite n *zero = refl

*-suc : ∀ x y → x * suc y ≃ x + x * y
*-suc zero n = refl
*-suc (suc x) y = begin
    suc x * suc y
  =[ refl ⟩
    suc (y + x * suc y)
  =[ cong suc (lemma x y) ⟩
    suc x + suc x * y
  ∎ where
  lemma : ∀ x y → y + x * suc y ≃ x + y + x * y
  lemma x y = begin
      y + x * suc y
    =[ cong (_+_ y) (*-suc x y) ⟩
      y + (x + x * y)
    =[ +-assoc y x (x * y) ⟩
      (y + x) + x * y
    =[ cong (flip _+_ (x * y)) (+-commute y x) ⟩
      (x + y) + x * y
    =[ sym (+-assoc x y (x * y)) ⟩
      x + y + x * y
    ∎

*-comm : ∀ m n → m * n ≃ n * m
*-comm x zero = x *zero
*-comm x (suc y) rewrite trans (*-suc x y) (cong (_+_ x) (*-comm x y)) = refl
