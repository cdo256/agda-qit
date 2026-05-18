open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties using (restrict-domain)
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set

module QIT.QW.Colimit.Properties {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  (ℓD ℓD' : Level)
  (P : Functor (PreorderCat I ≤p) (SetCat (ℓD ⊔ ℓD')))
  where

  private
    module ≤ = IsPreorder (≤p .proj₂)
    _≤_ : BinaryRel I ℓ≤
    _≤_ = ≤p .proj₁

  open import QIT.QW.Colimit.Base ≤p ℓD ℓD' P public

  open Functor P using () renaming (ob to P̂)
  module ≤p = QIT.Category.Preorder I ≤p
  open SetoidQuotient Colim

  RestrictDiagram : (α : I) → Functor (≤p.PreorderCat↓ α) (SetCat (ℓD ⊔ ℓD'))
  RestrictDiagram α = restrict-domain (≤p.include≤ α) P

  module Bounded (α : I) where
    open import QIT.QW.Colimit.Base (≤p.Restrict≤ α) ℓD ℓD' (RestrictDiagram α) public
      using ()
      renaming
        ( Colim₀ to Colim≤₀
        ; _≈ˡ_ to _≈ˡ≤_
        ; recˡ to recˡ≤
        ; ≈lrefl to ≈lrefl≤
        ; Colim to Colim≤~
        ; Colim/≈ to Colim≤
        ; ≈lstage to ≈l≤stage
        ; ≈lstep to ≈l≤step
        ; ≈lsym to ≈l≤sym
        ; ≈ltrans to ≈l≤trans
        )

    forget₀ : Colim≤₀ → Colim₀
    forget₀ (i≤α , x) = i≤α .fst , x

    forget≈≤ : ∀ {s t} → s ≈ˡ≤ t → forget₀ s ≈ˡ forget₀ t
    forget≈≤ (≈lstage i e) = ≈lstage (i .fst) e
    forget≈≤ (≈lstep p x) = ≈lstep p x
    forget≈≤ (≈lsym r) = ≈lsym (forget≈≤ r)
    forget≈≤ (≈ltrans r₁ r₂) = ≈ltrans (forget≈≤ r₁) (forget≈≤ r₂)

    recˡ≤' : ∀ {ℓ ℓ'}
         → (C≤ : ∀ {s t} → s ≈ˡ≤ t → Prop ℓ)
         → (C  : ∀ {s t} → s ≈ˡ t → Prop ℓ')
         → (c-stage : ∀ (i : ≤p.Below α) {x x'} (e : x ≡ x') → C≤ (≈l≤stage i e))
         → (c-step  : ∀ {i j : ≤p.Below α} (p : i .fst ≤ j .fst) (x : Functor.ob (RestrictDiagram α) i) → C≤ (≈l≤step p x))
         → (c-sym   : ∀ {s t} (r : s ≈ˡ≤ t) → C≤ r → C≤ (≈l≤sym r))
         → (c-trans : ∀ {s t u} (r₁ : s ≈ˡ≤ t) (r₂ : t ≈ˡ≤ u) → C≤ r₁ → C≤ r₂ → C≤ (≈l≤trans r₁ r₂))
         → (forgetC : ∀ {s t} (r : s ≈ˡ≤ t) → C≤ r → C (forget≈≤ r))
         → ∀ {s t} (r : s ≈ˡ≤ t) → C (forget≈≤ r)
    recˡ≤' C≤ C c-stage c-step c-sym c-trans forgetC r = forgetC r (go r)
      where
      go : ∀ {s t} (r : s ≈ˡ≤ t) → C≤ r
      go (≈lstage i e) = c-stage i e
      go (≈lstep {i} {j} p x) = c-step {i} {j} p x
      go (≈lsym r) = c-sym r (go r)
      go (≈ltrans r₁ r₂) = c-trans r₁ r₂ (go r₁) (go r₂)

  module _ where
    open Bounded renaming (_≈ˡ≤_ to _⊢_≈ˡ≤_)
    -- recˡ↑ : 
    -- recˡ↑ : ∀ {ℓ ℓ'}
    --      → (C≤ : ∀ α {s t} → α ⊢ s ≈ˡ≤ t → Prop ℓ)
    --      → (C  : ∀ {s t} → s ≈ˡ t → Prop ℓ')
    --      → (c-stage : ∀ α (i : ≤p.Below α) {x x' : ?} (e : x ≡ x') → C≤ α (≈l≤stage i e))
    --      → (c-step  : ∀ α {i j : ≤p.Below α} (p : i .fst ≤ j .fst) (x : Functor.ob (RestrictDiagram α) i) → C≤ α (≈l≤step p x))
    --      → (c-sym   : ∀ α {s t} (r : α ⊢ s ≈ˡ≤ t) → C≤ r → C≤ (≈l≤sym r))
    --      → (c-trans : ∀ α {s t u} (r₁ : α ⊢ s ≈ˡ≤ t) (r₂ : α ⊢ t ≈ˡ≤ u) → C≤ r₁ → C≤ r₂ → C≤ (≈l≤trans r₁ r₂))
    --      → (forgetC : ∀ α {s t} (r : α ⊢ s ≈ˡ≤ t) → C≤ r → C (forget≈≤ r))
    --      → ∀ {s t} (r : s ≈ˡ t) → C r
    -- recˡ↑ C≤ C c-stage c-step c-sym c-trans forgetC r = ?

  record Cocone : Set (lsuc (ℓ≤ ⊔ ℓD' ⊔ ℓD ⊔ ℓI)) where
    field
      Apex     : Set (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD')
      inj      : ∀ i → P̂ i → Apex
      commutes : ∀ {i j} (p : i ≤ j)
               → inj i ≡ (inj j ∘ Functor.hom P (box p))

  open Cocone

  LimitCocone : Cocone
  LimitCocone = record
    { Apex     = Colim /≈
    ; inj      = λ i x → [ i , x ]
    ; commutes = λ p → ≡.funExt λ x → ≈[ ≈lstep p x ]
    }

  record ColimMorphism (C C' : Cocone) : Set (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD') where
    field
      apexHom  : (C .Apex) → (C' .Apex)
      commutes : ∀ i → (apexHom ∘ C .inj i) ≡ (C' .inj i)

  open ColimMorphism

  record isLimitingCocone (C : Cocone) : Set (lsuc ℓI ⊔ lsuc ℓ≤ ⊔ lsuc ℓD ⊔ lsuc ℓD') where
    field
      hom    : ∀ C' → ColimMorphism C C'
      unique : ∀ C' → (F : ColimMorphism C C')
             → ∀ x̃ → F .apexHom x̃ ≡ hom C' .apexHom x̃

  module IsLimitingCocone (C' : Cocone) where
    module C' = Cocone C'

    open isLimitingCocone
    open ≈.Hom

    f₀ : Colim₀ → C'.Apex
    f₀ (i , x) = C'.inj i x

    isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y) → f₀ (i , x) ≡ f₀ (j , y)
    isRespecting (≈lstage i x≈y) = ≡.cong (C'.inj i) x≈y
    isRespecting {i} {j} {x} {y} (≈lstep p x) = ≡.funExt⁻ (C'.commutes p) x
    isRespecting (≈lsym r) = ≡.sym (isRespecting r)
    isRespecting (≈ltrans r s) = ≡.trans (isRespecting r) (isRespecting s)

    f : Colim /≈ → C'.Apex
    f = rec f₀ isRespecting

    F : ColimMorphism LimitCocone C'
    F .apexHom = f
    F .commutes i = ≡.refl

    unq : (G : ColimMorphism LimitCocone C') → ∀ x̃ → G .apexHom x̃ ≡ f x̃
    unq G = elimp (λ x̃ → G .apexHom x̃ ≡ f x̃) λ (i , x) → ≡.funExt⁻ (G .commutes i) x

  isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
  isLimitingCoconeLimitCocone = record
    { hom    = F
    ; unique = unq
    }
    where
    open IsLimitingCocone
