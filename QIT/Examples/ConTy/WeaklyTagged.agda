module QIT.Examples.ConTy.WeaklyTagged where

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

    ∙ : CT
    k∙ : [ ∙ ] ≡ ĉ
    ▷ : (γ : CT) (a : CT) → CT
    k▷ : (γ : CT) (a : CT)
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ ▷ γ a ] ≡ ĉ
    u : (γ : CT) → CT
    ku : (γ : CT)
      → [ γ ] ≡ ĉ
      → [ u γ ] ≡ t̂ γ 
    π : (γ : CT) (a : CT) (b : CT) → CT
    kπ : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ π γ a b ] ≡ t̂ γ 
    σ : (γ : CT) (a : CT) (b : CT) → CT
    kσ : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ σ γ a b ] ≡ t̂ γ 
    σ▷ : (γ : CT) (a : CT) (b : CT) (c : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ c ] ≡ t̂ (▷ (▷ γ a) b)
      → (▷ (σ γ a b) c)
      ≡ (▷ (▷ (▷ γ a) b) c)
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
    ▷ : ∀ (γ : α.CT) (a : α.CT) → θ (α.▷ γ a) ≡ β.▷ (θ γ) (θ a)
    u : ∀ (γ : α.CT) → θ (α.u γ) ≡ β.u (θ γ)
    π : ∀ (γ : α.CT) (a : α.CT) (b : α.CT)
      → θ (α.π γ a b) ≡ β.π (θ γ) (θ a) (θ b)
    σ : ∀ (γ : α.CT) (a : α.CT) (b : α.CT)
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
  ; ▷ = λ _ _ → ≡.refl
  ; u = λ _ → ≡.refl
  ; π = λ _ _ _ → ≡.refl
  ; σ = λ _ _ _ → ≡.refl
  }

_∘_ : ∀ {α β γ} → Hom β γ → Hom α β → Hom α γ
_∘_ g f = record
  { θ = λ x → g.θ (f.θ x)
  ; [_] = λ x → ≡.trans (≡.cong g.θ (f.[_] x)) (g.[_] (f.θ x))
  ; k̂ = ≡.trans (≡.cong g.θ f.k̂) g.k̂
  ; ĉ = ≡.trans (≡.cong g.θ f.ĉ) g.ĉ
  ; t̂ = λ x → ≡.trans (≡.cong g.θ (f.t̂ x)) (g.t̂ (f.θ x))
  ; ∙ = ≡.trans (≡.cong g.θ f.∙) g.∙
  ; ▷ = λ x a → ≡.trans (≡.cong g.θ (f.▷ x a)) (g.▷ (f.θ x) (f.θ a))
  ; u = λ x → ≡.trans (≡.cong g.θ (f.u x)) (g.u (f.θ x))
  ; π = λ x a b → ≡.trans (≡.cong g.θ (f.π x a b)) (g.π (f.θ x) (f.θ a) (f.θ b))
  ; σ = λ x a b → ≡.trans (≡.cong g.θ (f.σ x a b)) (g.σ (f.θ x) (f.θ a) (f.θ b))
  }
  where
  module f = Hom f
  module g = Hom g

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
