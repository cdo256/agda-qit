open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
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
      renaming
        ( Colim₀ to Colim≤₀
        ; _≈ˡ_ to _≈ˡ≤_
        ; recˡ to recˡ≤
        ; ≈lrefl to ≈lrefl≤
        ; Colim to Colim≤~
        ; Colim/≈ to Colim≤
        )

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
