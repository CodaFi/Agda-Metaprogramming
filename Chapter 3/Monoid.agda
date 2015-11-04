module Monoid where
  open import Basics
  open import Applicative
  open import Function using (const)
  
record Monoid (X : Set) : Set where
  infixr 4 _•_
  field
    ε : X
    _•_ : X → X → X
  monoidApplicative : Applicative λ _ → X
  monoidApplicative = record
    { pure = const Monoid.ε
    ; _⍟_ = _•_
    }
open Monoid {{...}} public

sumMonoid : Monoid ℕ
sumMonoid = record { ε = zero; _•_ = _+_ }

record MonoidOK X {{M : Monoid X}} : Set where
  field
    absorbL : (x : X) → ε • x ≃ x
    absorbR : (x : X) → x • ε ≃ x
    assoc   : (x y z : X) → (x • y) • z ≃ x • (y • z)
open MonoidOK {{...}} public

natMonoidOK : MonoidOK ℕ {{sumMonoid}}
natMonoidOK = record
  { absorbL = λ _ → refl
  ; absorbR = _+zero
  ; assoc = assoc+
  } where
    _+zero : ∀ x → x + zero ≃ x
    zero +zero = refl
    suc n +zero rewrite n +zero = refl

    assoc+ : ∀ x y z → (x + y) + z ≃ x + (y + z)
    assoc+ zero y z = refl
    assoc+ (suc x) y z rewrite assoc+ x y z = refl

record MonoidHom {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}} (f : X → Y) : Set where
  field
    respε : f ε ≃ ε
    resp• : ∀ x x' → f (x • x') ≃ f x • f x'
open MonoidHom {{...}} public

monoidApplicativeHom : ∀ {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}} (f : X -> Y){{hf : MonoidHom f}} ->
  AppHom {{monoidApplicative {{MX}}}} {{monoidApplicative {{MY}}}} f
monoidApplicativeHom f {{hf}} = record
  {  respPure  = \ x -> MonoidHom.respε hf
  ;  respApp   = MonoidHom.resp• hf
  }

homSum : ∀ {F G}{{AF : Applicative F}}{{AG : Applicative G}} → (f : F -:> G) → Applicative λ X → F X ⊎ G X
homSum {F}{G}{{AF}}{{AG}} f = record {
  pure = λ x → tt , (pure {{AF}} x)
  ; _⍟_ = app
  } where
    app : {S T : Set} → Sg Two (F (S → T) ⟨?⟩ G (S → T)) → Sg Two (F S ⟨?⟩ G S) → Sg Two (F T ⟨?⟩ G T)
    app (tt , k) (tt , g) = tt , (k ⍟ g)
    app (tt , k) (ff , g) = ff , (f k ⍟ g)
    app (ff , k) (tt , g) = ff , (k ⍟ (f g))
    app (ff , k) (ff , g) = ff , (k ⍟ g)

{-
homSumOKP : ∀ {F G}{{AF : Applicative F}}{{AG : Applicative G}} → ApplicativeOKP F → ApplicativeOKP G → (f : F -:> G) -> AppHom f → ApplicativeOKP _ {{homSum f}}
homSumOKP {F}{G}{{AF}}{{AG}} FOK GOK f homf = record
  { lawId = lawIdLemma
  ; lawCo = lawCoLemma
  ; lawHom = {!!}
  ; lawCom = {!!}
  } where
    lawIdLemma : {X : Set} -> (x : F X ⊎ G X) ->
                 _⍟_ {{homSum f}} (pure {{homSum f}} id) x ≃ x
    lawIdLemma (tt , u) = tt , (AF Applicative.Applicative.⍟ Applicative.Applicative.pure AF id) u
                            =[ cong (_,_ tt) (ApplicativeOKP.lawId FOK u) ⟩
                          (tt , u)
                            ∎
    lawIdLemma (ff , u) = ff , (AG Applicative.Applicative.⍟ f (Applicative.Applicative.pure AF id)) u
                             =[ cong (λ q → ff , (q ⍟ u)) (AppHom.respPure homf id) ⟩
                          ff , (AG Applicative.Applicative.⍟ Applicative.Applicative.pure AG id) u
                             =[ cong (_,_ ff) (ApplicativeOKP.lawId GOK u) ⟩
                          (ff , u)
                             ∎
    comp : {A B C : Set} → (B → C) → (A → B) → A → C
    comp f g x = f (g x)
    
    lawCoLemma :  {R S T : Set} (g : F (S → T) ⊎ G (S → T)) (h : F (R → S) ⊎ G (R → S)) (r : F R ⊎ G R) →
      _⍟_ {{homSum f}}
       (_⍟_ {{homSum f}}
        (_⍟_ {{homSum f}} (pure {{homSum f}} (λ g h → g ∘ h)) g) h) r ≃ _⍟_ {{homSum f}} g (_⍟_ {{homSum f}} h r)
    lawCoLemma (tt , g) (tt , h) (tt , r) =
      tt , _⍟_ {{AF}} ( _⍟_ {{AF}} (_⍟_ {{AF}} (pure {{AF}} (λ g h → g ∘ h)) g) h) r
        =[ cong (λ q → tt , q) (ApplicativeOKP.lawCo FOK g h r) ⟩
      tt , (_⍟_ {{AF}} g) (_⍟_ {{AF}} h r)
        ∎
    lawCoLemma (tt , g) (tt , h) (ff , r) =
      ff , (AG Applicative.Applicative.⍟ f ((AF Applicative.Applicative.⍟ (AF Applicative.Applicative.⍟ Applicative.Applicative.pure AF comp) g) h)) r
        =[ cong (λ q → ff , (_⍟_ {{AG}} q r)) (AppHom.respApp homf ((_⍟_ {{AF}} (pure {{AF}} (λ j k a → j (k a))) g)) h) ⟩
      ff , (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ f ((AF Applicative.Applicative.⍟ Applicative.Applicative.pure AF comp) g)) (f h)) r
        =[ cong (λ q → ff , (AG Applicative.Applicative.⍟ (_⍟_ {{AG}} q) (f h)) r) (AppHom.respApp homf (Applicative.Applicative.pure AF comp) g) ⟩
      ff , (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ (f ((Applicative.Applicative.pure AF comp)))) (f g)) (f h)) r
        =[ cong (λ q → ff , (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ q) (f g)) (f h)) r) (AppHom.respPure homf (λ g h → g ∘ h) ) ⟩
      ff , (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ (AG Applicative.Applicative.⍟ Applicative.Applicative.pure AG comp) (f g)) (f h)) r
        =[ cong (λ q → ff , q) ((ApplicativeOKP.lawCo GOK (f g) (f h) r)) ⟩
      ff , (AG Applicative.Applicative.⍟ f g) ((AG Applicative.Applicative.⍟ f h) r)
        ∎
    lawCoLemma (tt , g) (ff , h) (tt , r) = {!!}
    lawCoLemma (tt , g) (ff , h) (ff , r) = {!!}
    lawCoLemma (ff , g) (tt , h) (tt , r) = {!!}
    lawCoLemma (ff , g) (tt , h) (ff , r) = {!!}
    lawCoLemma (ff , g) (ff , h) (tt , r) = {!!}
    lawCoLemma (ff , g) (ff , h) (ff , r) = {!!}
-}
