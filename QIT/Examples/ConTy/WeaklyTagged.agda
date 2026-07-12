open import QIT.Prelude

module QIT.Examples.ConTy.WeaklyTagged
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base

record Algebra ℓX : Set (lsuc ℓX) where
  field
    CT : Set ℓX
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

record Hom {ℓX} (A B : Algebra ℓX) : Set ℓX where
  private
    module A = Algebra A
    module B = Algebra B
  field
    θ : A.CT → B.CT
    [_] : ∀ (x : A.CT) → θ (A.[ x ]) ≡ B.[ θ x ]
    k̂ : θ A.k̂ ≡ B.k̂
    ĉ : θ A.ĉ ≡ B.ĉ
    t̂ : ∀ (γ : A.CT) → θ (A.t̂ γ) ≡ B.t̂ (θ γ)
    ∙ : θ A.∙ ≡ B.∙
    ▷ : ∀ (γ : A.CT) (a : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → A.[ a ] ≡ A.t̂ γ
      → θ (A.▷ γ a) ≡ B.▷ (θ γ) (θ a)
    u : ∀ (γ : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → θ (A.u γ) ≡ B.u (θ γ)
    π : ∀ (γ : A.CT) (a : A.CT) (b : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → A.[ a ] ≡ A.t̂ γ
      → A.[ b ] ≡ A.t̂ (A.▷ γ a)
      → θ (A.π γ a b) ≡ B.π (θ γ) (θ a) (θ b)
    σ : ∀ (γ : A.CT) (a : A.CT) (b : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → A.[ a ] ≡ A.t̂ γ
      → A.[ b ] ≡ A.t̂ (A.▷ γ a)
      → θ (A.σ γ a b) ≡ B.σ (θ γ) (θ a) (θ b)

open Hom public

id : ∀ {ℓX} {A : Algebra ℓX} → Hom A A
id {ℓX} = record
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

_∘_ : ∀ {ℓX} {A B C : Algebra ℓX} → Hom B C → Hom A B → Hom A C
_∘_ {ℓX} {A} {B} {C} g f = record
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

record _≈_ {ℓX} {A B : Algebra ℓX} (f g : Hom A B) : Prop ℓX where
  constructor mk≈
  field
    θ≡ : ∀ x → f .θ x ≡ g .θ x

open _≈_ public

isEquiv≈ : ∀ {ℓX} {A B : Algebra ℓX} → IsEquivalence (_≈_ {ℓX} {A} {B})
isEquiv≈ = record
  { refl = mk≈ λ _ → ≡.refl
  ; sym = λ (mk≈ p) → mk≈ λ x → ≡.sym (p x)
  ; trans = λ (mk≈ p) (mk≈ q) → mk≈ λ x → ≡.trans (p x) (q x)
  }

∘-resp-≈ : ∀ {ℓX} {A B γ : Algebra ℓX} {f h : Hom B γ} {g i : Hom A B}
  → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} (mk≈ p) (mk≈ q) =
  mk≈ λ x → ≡.trans (≡.cong (f .θ) (q x)) (p (i .θ x))

Cat : ∀ ℓX → Category (lsuc ℓX) ℓX ℓX
Cat ℓX = record
  { Obj = Algebra ℓX
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

-- open import QIT.Category.Morphism Cat public
-- open import QIT.Category.Initial Cat public
