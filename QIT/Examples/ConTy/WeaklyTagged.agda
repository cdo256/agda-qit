open import QIT.Prelude

module QIT.Examples.ConTy.WeaklyTagged ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base

record Algebra : Set₁ where
  field
    CT : Set
    [_] : CT → CT
    k̂ : CT
    kk̂ : [ k̂ ] ≡ k̂
    ĉ : CT
    kĉ : [ ĉ ] ≡ k̂
    t̂ : (γ : CT) → CT
    kt̂ : (γ : CT)
      → [ γ ] ≡ ĉ
      → [ t̂ γ ] ≡ k̂
    t̂-γ : (γ : CT) (a : CT)
      → [ a ] ≡ t̂ γ
      → [ γ ] ≡ ĉ

    ∙ : CT
    k∙ : [ ∙ ] ≡ ĉ
    ▷ : (γ : CT) (a : CT) → CT
    k▷ : (γ : CT) (a : CT)
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ ▷ γ a ] ≡ ĉ
    k▷-a : (γ : CT) (a : CT)
      → [ γ ] ≡ ĉ
      → [ ▷ γ a ] ≡ ĉ
      → [ a ] ≡ t̂ γ
    u : (γ : CT) → CT
    ku : (γ : CT)
      → [ γ ] ≡ ĉ
      → [ u γ ] ≡ t̂ γ 
    π : (γ : CT) (a : CT) (b : CT) → CT
    kπ-a : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ π γ a b ] ≡ t̂ γ 
      → [ a ] ≡ t̂ γ
    kπ-b : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ π γ a b ] ≡ t̂ γ 
      → [ b ] ≡ t̂ (▷ γ a)
    kπ : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ π γ a b ] ≡ t̂ γ 
    σ : (γ : CT) (a : CT) (b : CT) → CT
    kσ-a : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ σ γ a b ] ≡ t̂ γ 
      → [ a ] ≡ t̂ γ
    kσ-b : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ σ γ a b ] ≡ t̂ γ 
      → [ b ] ≡ t̂ (▷ γ a)
    kσ : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ σ γ a b ] ≡ t̂ γ 
    σ▷ : (γ : CT) (a : CT) (b : CT)
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → ▷ (▷ γ a) b
      ≡ ▷ γ (σ γ a b)
    σπ : (γ : CT)
      → (a : CT) 
      → (b : CT) 
      → (c : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ c ] ≡ t̂ (▷ (▷ γ a) b)
      → π γ a (π (▷ γ a) b c)
      ≡ π γ (σ γ a b) c

record Hom (α β : Algebra) : Set₁ where
  private
    module α = Algebra α
    module β = Algebra β
  field
    θ : α.CT → β.CT
    [_] : ∀ (x : α.CT) → θ (α.[ x ]) ≡ β.[ θ x ]
    k̂ : θ α.k̂ ≡ β.k̂
    ĉ : θ α.ĉ ≡ β.ĉ
    t̂ : ∀ (γ : α.CT) → θ (α.t̂ γ) ≡ β.t̂ (θ γ)
    ∙ : θ α.∙ ≡ β.∙
    ▷ : ∀ (γ : α.CT) (a : α.CT)
      → α.[ γ ] ≡ α.ĉ
      → α.[ a ] ≡ α.t̂ γ
      → θ (α.▷ γ a) ≡ β.▷ (θ γ) (θ a)
    u : ∀ (γ : α.CT)
      → α.[ γ ] ≡ α.ĉ
      → θ (α.u γ) ≡ β.u (θ γ)
    π : ∀ (γ : α.CT) (a : α.CT) (b : α.CT)
      → α.[ γ ] ≡ α.ĉ
      → α.[ a ] ≡ α.t̂ γ
      → α.[ b ] ≡ α.t̂ (α.▷ γ a)
      → θ (α.π γ a b) ≡ β.π (θ γ) (θ a) (θ b)
    σ : ∀ (γ : α.CT) (a : α.CT) (b : α.CT)
      → α.[ γ ] ≡ α.ĉ
      → α.[ a ] ≡ α.t̂ γ
      → α.[ b ] ≡ α.t̂ (α.▷ γ a)
      → θ (α.σ γ a b) ≡ β.σ (θ γ) (θ a) (θ b)

open Hom public

id : ∀ {α} → Hom α α
id = record
  { θ = λ x → x
  ; [_] = λ _ → ≡.refl
  ; k̂ = ≡.refl
  ; ĉ = ≡.refl
  ; t̂ = λ _ → ≡.refl
  ; ∙ = ≡.refl
  ; ▷ = λ _ _ _ _ → ≡.refl
  ; u = λ _ _ → ≡.refl
  ; π = λ _ _ _ _ _ _ → ≡.refl
  ; σ = λ _ _ _ _ _ _ → ≡.refl
  }

_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ {A} {B} {C} g f = record
  { θ = λ x → g.θ (f.θ x)
  ; [_] = λ x → ≡.trans (≡.cong g.θ (f.[_] x)) (g.[_] (f.θ x))
  ; k̂ = ≡.trans (≡.cong g.θ f.k̂) g.k̂
  ; ĉ = ≡.trans (≡.cong g.θ f.ĉ) g.ĉ
  ; t̂ = λ x → ≡.trans (≡.cong g.θ (f.t̂ x)) (g.t̂ (f.θ x))
  ; ∙ = ≡.trans (≡.cong g.θ f.∙) g.∙
  ; ▷ = λ x a kx ka → ≡.trans (≡.cong g.θ (f.▷ x a kx ka)) (g.▷ (f.θ x) (f.θ a) (kx' x kx) (ka' x a ka))
  ; u = λ x kx → ≡.trans (≡.cong g.θ (f.u x kx)) (g.u (f.θ x) (kx' x kx))
  ; π = λ x a b kx ka kb → ≡.trans (≡.cong g.θ (f.π x a b kx ka kb)) (g.π (f.θ x) (f.θ a) (f.θ b) (kx' x kx) (ka' x a ka) (kb' x a b kx ka kb))
  ; σ = λ x a b kx ka kb → ≡.trans (≡.cong g.θ (f.σ x a b kx ka kb)) (g.σ (f.θ x) (f.θ a) (f.θ b) (kx' x kx) (ka' x a ka) (kb' x a b kx ka kb))
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module g = Hom g

  kx' : ∀ x → A.[ x ] ≡ A.ĉ → B.[ f.θ x ] ≡ B.ĉ
  kx' x kx = ≡.trans (≡.sym (f.[_] x)) (≡.trans (≡.cong f.θ kx) f.ĉ)

  ka' : ∀ x a → A.[ a ] ≡ A.t̂ x → B.[ f.θ a ] ≡ B.t̂ (f.θ x)
  ka' x a ka = ≡.trans (≡.sym (f.[_] a)) (≡.trans (≡.cong f.θ ka) (f.t̂ x))

  kb' : ∀ x a b
    → A.[ x ] ≡ A.ĉ
    → A.[ a ] ≡ A.t̂ x
    → A.[ b ] ≡ A.t̂ (A.▷ x a)
    → B.[ f.θ b ] ≡ B.t̂ (B.▷ (f.θ x) (f.θ a))
  kb' x a b kx ka kb =
    ≡.trans
      (≡.trans (≡.sym (f.[_] b)) (≡.trans (≡.cong f.θ kb) (f.t̂ (A.▷ x a))))
      (≡.cong B.t̂ (f.▷ x a kx ka))

record _≈_ {α β : Algebra} (f g : Hom α β) : Prop ℓ0 where
  constructor mk≈
  field
    θ≡ : ∀ x → f .θ x ≡ g .θ x

open _≈_ public

isEquiv≈ : ∀ {α β : Algebra} → IsEquivalence (_≈_ {α} {β})
isEquiv≈ = record
  { refl = mk≈ λ _ → ≡.refl
  ; sym = λ (mk≈ p) → mk≈ λ x → ≡.sym (p x)
  ; trans = λ (mk≈ p) (mk≈ q) → mk≈ λ x → ≡.trans (p x) (q x)
  }

∘-resp-≈ : ∀ {α β γ : Algebra} {f h : Hom β γ} {g i : Hom α β}
  → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} (mk≈ p) (mk≈ q) =
  mk≈ λ x → ≡.trans (≡.cong (f .θ) (q x)) (p (i .θ x))

Cat : Category (lsuc ℓ0) (lsuc ℓ0) ℓ0
Cat = record
  { Obj = Algebra
  ; _⇒_ = Hom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = mk≈ λ _ → ≡.refl
  ; sym-assoc = mk≈ λ _ → ≡.refl
  ; identityˡ = mk≈ λ _ → ≡.refl
  ; identityʳ = mk≈ λ _ → ≡.refl
  ; identity² = mk≈ λ _ → ≡.refl
  ; equiv = isEquiv≈
  ; ∘-resp-≈ = ∘-resp-≈
  }

open import QIT.Category.Morphism Cat public
open import QIT.Category.Initial Cat public

-- Q : Algebra
-- isInitialQ : isInitial Q
