module QIT.Examples.ConTy.TaggedAlgebra where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base

-- "Tagged" / "mutual" presentation of ConTy algebras.
-- Instead of Ty : Con → Set (a dependent family), we have a flat
-- Ty∙ : Set together with a tagging map ty-con : Ty∙ → Con that
-- records the context each type lives in.  All operations are total
-- (no context constraints built into their types); the context
-- invariants are expressed as separate equational fields.

record Algebra : Set₁ where
  field
    Con    : Set
    Ty∙    : Set
    ty-con : Ty∙ → Con

    ∙      : Con
    _▷_    : Con → Ty∙ → Con   -- unconstrained; context invariant via ty-con
    ι      : Con → Ty∙
    π      : Con → Ty∙ → Ty∙ → Ty∙

    -- Context invariants
    ι-con  : ∀ Γ     → ty-con (ι Γ) ≡ Γ
    π-con  : ∀ Γ A B → ty-con (π Γ A B) ≡ Γ

open Algebra public

-- A morphism preserves all operations and the tagging map.
record Hom (A B : Algebra) : Set₁ where
  private
    module A = Algebra A
    module B = Algebra B
  field
    conʰ    : A.Con  → B.Con
    tyʰ     : A.Ty∙  → B.Ty∙
    -- Naturality: tyʰ respects the tagging
    ty-conʰ : ∀ T → B.ty-con (tyʰ T) ≡ conʰ (A.ty-con T)
    ∙ʰ      : conʰ A.∙ ≡ B.∙
    ▷ʰ      : ∀ Γ T → conʰ (Γ A.▷ T) ≡ conʰ Γ B.▷ tyʰ T
    ιʰ      : ∀ Γ   → tyʰ (A.ι Γ) ≡ B.ι (conʰ Γ)
    πʰ      : ∀ Γ A B → tyʰ (A.π Γ A B) ≡ B.π (conʰ Γ) (tyʰ A) (tyʰ B)

id : ∀ {A} → Hom A A
id = record
  { conʰ    = λ Γ → Γ
  ; tyʰ     = λ T → T
  ; ty-conʰ = λ _ → ≡.refl
  ; ∙ʰ      = ≡.refl
  ; ▷ʰ      = λ _ _ → ≡.refl
  ; ιʰ      = λ _ → ≡.refl
  ; πʰ      = λ _ _ _ → ≡.refl
  }

_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ {A} {B} {C} g f = record
  { conʰ    = λ Γ → g.conʰ (f.conʰ Γ)
  ; tyʰ     = λ T → g.tyʰ (f.tyʰ T)
  ; ty-conʰ = λ T → ≡.trans (g.ty-conʰ (f.tyʰ T)) (≡.cong g.conʰ (f.ty-conʰ T))
  ; ∙ʰ      = ≡.trans (≡.cong g.conʰ f.∙ʰ) g.∙ʰ
  ; ▷ʰ      = λ Γ T → ≡.trans (≡.cong g.conʰ (f.▷ʰ Γ T)) (g.▷ʰ (f.conʰ Γ) (f.tyʰ T))
  ; ιʰ      = λ Γ   → ≡.trans (≡.cong g.tyʰ (f.ιʰ Γ)) (g.ιʰ (f.conʰ Γ))
  ; πʰ      = λ Γ A B →
      ≡.trans (≡.cong g.tyʰ (f.πʰ Γ A B))
              (g.πʰ (f.conʰ Γ) (f.tyʰ A) (f.tyʰ B))
  }
  where
  module f = Hom f
  module g = Hom g

-- Morphism equality: pointwise on both Con and Ty∙.
-- Because tyʰ is a flat (non-dependent) function the equality is
-- simple – no need for dsym / dtrans.
record _≈_ {A B : Algebra} (f g : Hom A B) : Prop ℓ0 where
  private
    module f = Hom f
    module g = Hom g
  field
    con≡ : ∀ Γ → f.conʰ Γ ≡ g.conʰ Γ
    ty≡  : ∀ T → f.tyʰ T ≡ g.tyʰ T

open _≈_

isEquiv≈ : ∀ {A B : Algebra} → IsEquivalence (_≈_ {A} {B})
isEquiv≈ = record
  { refl  = record
    { con≡ = λ _ → ≡.refl
    ; ty≡  = λ _ → ≡.refl
    }
  ; sym   = λ p → record
    { con≡ = λ Γ → ≡.sym (con≡ p Γ)
    ; ty≡  = λ T → ≡.sym (ty≡  p T)
    }
  ; trans = λ p q → record
    { con≡ = λ Γ → ≡.trans (con≡ p Γ) (con≡ q Γ)
    ; ty≡  = λ T → ≡.trans (ty≡  p T) (ty≡  q T)
    }
  }

∘-resp-≈ : ∀ {A B C : Algebra} {f h : Hom B C} {g i : Hom A B}
          → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} p q = record
  { con≡ = λ Γ →
      ≡.trans (≡.cong (Hom.conʰ f) (con≡ q Γ))
              (con≡ p (Hom.conʰ i Γ))
  ; ty≡  = λ T →
      ≡.trans (≡.cong (Hom.tyʰ f) (ty≡ q T))
              (ty≡ p (Hom.tyʰ i T))
  }

Cat : Category (lsuc ℓ0) (lsuc ℓ0) ℓ0
Cat = record
  { Obj       = Algebra
  ; _⇒_       = Hom
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; sym-assoc = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; identityˡ = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; identityʳ = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; identity² = record { con≡ = λ _ → ≡.refl ; ty≡ = λ _ → ≡.refl }
  ; equiv     = isEquiv≈
  ; ∘-resp-≈  = ∘-resp-≈
  }
