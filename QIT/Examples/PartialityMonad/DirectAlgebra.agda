module QIT.Examples.PartialityMonad.DirectAlgebra where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Relation.Binary
open import QIT.Category.Base
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

record Algebra : Set₁ where
  infix 4 _≤_

  field
    A⊥ : Set
    _≤_ : A⊥ → A⊥ → Set

    η : Bool → A⊥
    ⊥ : A⊥
    ⨆ : (a : ℕ → A⊥) → (inc : ∀ i → a i ≤ a (suc i)) → A⊥
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a inc i → a i ≤ ⨆ a inc
    ⨆≤ : ∀ a inc x → (∀ i → a i ≤ x) → ⨆ a inc ≤ x
    antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

record Hom (A B : Algebra) : Set₁ where
  module A = Algebra A
  module B = Algebra B
  open A using () renaming (A⊥ to A₀)
  open B using () renaming (A⊥ to B₀)
  field
    f : A₀ → B₀
    η : ∀ b → f (A.η b) ≡ B.η b
    ⊥ : f A.⊥ ≡ B.⊥
    ≤ : ∀ {x y} → x A.≤ y → f x B.≤ f y
    ⨆ : ∀ a inc → f (A.⨆ a inc)
      ≡ B.⨆ (λ i → f (a i)) (λ i → ≤ (inc i))

id : ∀ {A} → Hom A A
id = record
  { f = λ z → z
  ; η = λ _ → ≡.refl
  ; ⊥ = ≡.refl
  ; ≤ = λ p → p
  ; ⨆ = λ _ _ → ≡.refl }

_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ {A} {B} {C} g f = record
  { f = λ x → g₀ (f₀ x)
  ; η = λ b → ≡.trans (≡.cong g₀ (f.η b)) (g.η b)
  ; ⊥ = ≡.trans (≡.cong g₀ f.⊥) g.⊥
  ; ≤ = λ {x} {y} p → g.≤ (f.≤ p)
  ; ⨆ = {!!} }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  open A using () renaming (A⊥ to A₀)
  open B using () renaming (A⊥ to B₀)
  open C using () renaming (A⊥ to C₀)
  module f = Hom f
  module g = Hom g
  open f renaming (f to f₀)
  open g renaming (f to g₀)
    
record _≈_ {A B} (f g : Hom A B) : Prop₁ where
  constructor mk≈
  module f = Hom f
  module g = Hom g
  field
    f≡ : ∀ a → f.f a ≡ g.f a

isEquiv≈ : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
isEquiv≈ = record
  { refl = mk≈ (λ _ → ≡.refl)
  ; sym = λ (mk≈ p) → mk≈ λ a → ≡.sym (p a)
  ; trans = λ (mk≈ p) (mk≈ q)
          → mk≈ λ a → ≡.trans (p a) (q a) }

Cat : Category {!!} {!!} {!!}
Cat = record
  { Obj = Algebra
  ; _⇒_ = Hom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = {!!}
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = {!!}
  ; ∘-resp-≈ = {!!}
  }
