module Meta.Control.Traversable where

open import Meta.Basics
open import Meta.Data.EndoFunctor
open import Meta.Control.Applicative
open import Meta.Data.Monoid
open import Meta.Data.Vector

record Traversable (F : Set → Set) : Set₁ where
  field
    traverse : ∀ { G S T }{{ AG : Applicative G }} → (S → G T) -> F S → G (F T)

  -- Sweet Jesus, this is ugly.
  endofunctor : EndoFunctor F
  endofunctor = record { map = λ {S}{T} f fs → traverse {id}{S}{T}{{record { pure = id; _⍟_ = id }}} f fs  }
open Traversable {{...}} public

crush : ∀ { F X Y }{{ TF : Traversable F }}{{ M : Monoid Y }} → (X → Y) → F X → Y
crush {{ M = M }} = traverse { T = One }{{ AG = monoidApplicative {{ M }} }}

traversableId : Traversable id
traversableId = record { traverse = id }

traversableComp : ∀ { F G } → Traversable F → Traversable G → Traversable (F ∘ G)
traversableComp {F} {G} f g = record { traverse = traverse {{f}} ∘ traverse {{g}} }

traversableVec : forall {n} → Traversable (λ X → Vec X n)
traversableVec = record { traverse = vtr } where
  vtr : forall {n G S T} {{_ : Applicative G}} → (S → G T) → Vec S n → G (Vec T n)
  vtr {{aG}} f ⟨⟩ = pure ⟨⟩
  vtr {{aG}} f (x , xs) = pure {{aG}} _,_ ⍟ f x ⍟ vtr f xs
  
transpose : ∀ {m n X} → Vec (Vec X n) m → Vec (Vec X m) n
transpose = traverse {{traversableVec}}{{applicativeVec}} id


record TraversableOKP F {{TF : Traversable F}} : Set₁ where
  field
    -- lawPId   : ∀ {X}(xs : F X) → traverse {{TF}}{{_}} id xs ≃ xs
    lawPCo   : ∀ {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                       {R S T}(g : S → G T)(h : R → H S)(rs : F R) →
               let EH : EndoFunctor H ; EH = applicativeEndoFunctor
               in  map{H} (traverse g) (traverse h rs)
                      ≃
                    traverse{{TF}}{{applicativeComp AH AG}} (map{H} g ∘ h) rs
    lawPHom  : ∀ {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                      (h : G -:> H){S T}(g : S → G T) → AppHom h →
                      (ss : F S) →
                      traverse (h ∘ g) ss ≃ h (traverse g ss)
open TraversableOKP {{...}} public
