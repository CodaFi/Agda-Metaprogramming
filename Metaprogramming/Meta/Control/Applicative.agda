module Meta.Control.Applicative where

open import Meta.Basics
open import Meta.Data.EndoFunctor
  
record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⍟_
  field
    pure : ∀ { X } → X → F X
    _⍟_ : ∀ { S T } → F (S → T) → F S → F T

  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _⍟_ ∘ pure }
open Applicative {{...}} public                        

record ApplicativeOKP F {{AF : Applicative F}} : Set₁ where
  field
    lawId : ∀ {X} (x : F X) → pure {{AF}} id ⍟ x ≃ x
    lawCo : ∀ {R S T} (f : F (S → T))(g : F (R → S))(r : F R) → pure {{AF}} (λ f g → f ∘ g) ⍟ f ⍟ g ⍟ r ≃ f ⍟ (g ⍟ r)
    lawHom : ∀ {S T} (f : S → T)(s : S) → pure {{AF}} f ⍟ pure s ≃ pure (f s)
    lawCom : ∀ {S T} (f : F (S → T))(s : S) → f ⍟ pure s ≃ pure {{AF}} (λ f → f s) ⍟ f

  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    { endoFunctorId = lawId
    ; endoFunctorCo = λ f g r → pure {{AF}} f ⍟ (pure {{AF}} g ⍟ r)
                                  ⟨ lawCo (pure f) (pure g) r ]=
                                pure {{AF}} (λ f g → f ∘ g) ⍟ pure f ⍟ pure g ⍟ r
                                  =[ cong (λ x → x ⍟ pure g ⍟ r) (lawHom (λ f g → f ∘ g) f) ⟩
                                pure {{AF}} (_∘_ f) ⍟ pure g ⍟ r
                                  =[ cong (λ x → x ⍟ r) (lawHom (_∘_ f) g) ⟩
                                pure {{AF}} (f ∘ g) ⍟ r
                                  ∎
    }
open ApplicativeOKP {{...}} public

applicativeFun : ∀ { S } → Applicative λ X → S → X
applicativeFun = record
  { pure = λ x _ → x
  ; _⍟_ = λ s f k → s k (f k)
  }

applicativeId : Applicative id
applicativeId = record
  { pure = id
  ; _⍟_ = id
  }
    
applicativeComp : ∀ { F G } → Applicative F → Applicative G → Applicative (F ∘ G)
applicativeComp {F} {G} f g = record
  { pure = pure ∘ pure
  ; _⍟_ = λ k x → (f Applicative.⍟ (f Applicative.⍟ pure _⍟_) k) x
  }

data Product (F G : Set -> Set) (X : Set) : Set where
  prod : F X -> G X -> Product F G X
  
applicativeProd : ∀ { F G } → Applicative F → Applicative G → Applicative (Product F G)
applicativeProd { F } { G } aF aG = record
  { pure = λ z → prod (pure z) (pure z)
  ; _⍟_ = appProd
  }
  where
    appProd : ∀ { S T } → Product F G (S → T) → Product F G S → Product F G T
    appProd (prod f g) (prod x y) = prod (f ⍟ x) (g ⍟ y)

_-:>_ : ∀ (F G : Set → Set) → Set₁
F -:> G = ∀ {X} → F X → G X

record AppHom  {F}{{AF : Applicative F}}{G}{{AG : Applicative G}}
               (k : F -:> G) : Set1 where
  field
    respPure  : forall {X}(x : X) -> k (pure x) ≃ pure x
    respApp   : forall {S T}(f : F (S -> T))(s : F S) -> k (f ⍟ s) ≃ k f ⍟ k s
