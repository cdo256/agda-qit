{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid
open import Data.Product
import QIT.Diagram

module QIT.Colimit {ℓI} {ℓ≤} {ℓB} {ℓB'}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  (P : QIT.Diagram.Diagram ≤p)
  where

  open QIT.Diagram ≤p
  open Diagram P renaming (D-ob to P̂)

  Pf : ∀ {i j} (p : i ≤ j) → (⟨ P̂ i ⟩ → ⟨ P̂ j ⟩)
  Pf p = to
    where open ≈.Hom (D-mor p)

  -- The carrier of the colimit (Sigma type)
  Colim₀ : Set (ℓI ⊔ ℓB)
  Colim₀ = Σ[ i ∈ I ] ⟨ P̂ i ⟩

  -- data _≈ˡ'_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓB ⊔ ℓB') where
  --   ≈lstage' : ∀ i → {x x' : ⟨ P̂ i ⟩} → P̂ i [ x ≈ x' ]
  --            → (i , x) ≈ˡ' (i , x')
  --   ≈lstep   : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → (i , x) ≈ˡ' (j , Pf p x)
  --   ≈lsym    : ∀ {s t} → s ≈ˡ' t → t ≈ˡ' s
  --   ≈ltrans  : ∀ {s t u} → s ≈ˡ' t → t ≈ˡ' u → s ≈ˡ' u

  -- The equivalence relation generating the colimit
  data _≈ˡ_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓB ⊔ ℓB') where
    ≈lstage : ∀ i → {x x' : ⟨ P̂ i ⟩} → P̂ i [ x ≈ x' ]
            → (i , x) ≈ˡ (i , x')
    ≈lstep  : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → (i , x) ≈ˡ (j , Pf p x)
    ≈lsym   : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
    ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u

  recˡ : ∀ {ℓ} (C : ∀ {s t} → s ≈ˡ t → Prop ℓ)
       → (c-stage : ∀ i {x x'} (e : P̂ i [ x ≈ x' ]) → C (≈lstage i e))
       → (c-step  : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → C (≈lstep p x))
       → (c-sym   : ∀ {s t} (r : s ≈ˡ t) → C r → C (≈lsym r))
       → (c-trans : ∀ {s t u} (r₁ : s ≈ˡ t) (r₂ : t ≈ˡ u) → C r₁ → C r₂ → C (≈ltrans r₁ r₂))
       → ∀ {s t} (r : s ≈ˡ t) → C r
  recˡ C c-stage c-step c-sym c-trans = go
    where
      go : ∀ {s t} (r : s ≈ˡ t) → C r
      go (≈lstage i e)    = c-stage i e
      go (≈lstep p x)     = c-step p x
      go (≈lsym r)        = c-sym r (go r)
      go (≈ltrans r₁ r₂)  = c-trans r₁ r₂ (go r₁) (go r₂)

  -- ≈ˡ→≈ˡ' : ∀ {i j x y} → (i , x) ≈ˡ (j , y) → (i , x) ≈ˡ' (j , y)
  -- ≈ˡ→≈ˡ' (≈lstage i i ≡.refl {x} {x'} q) = ≈lstage' i q
  -- ≈ˡ→≈ˡ' (≈lstep p x) = ≈lstep p x
  -- ≈ˡ→≈ˡ' (≈lsym p) = ≈lsym (≈ˡ→≈ˡ' p)
  -- ≈ˡ→≈ˡ' (≈ltrans p p₁) = ≈ltrans (≈ˡ→≈ˡ' p) (≈ˡ→≈ˡ' p₁)

  -- ≈ˡ'→≈ˡ : ∀ {i j x y} → (i , x) ≈ˡ' (j , y) → (i , x) ≈ˡ (j , y)
  -- ≈ˡ'→≈ˡ (≈lstage' i q) = ≈lstage i i ≡.refl q
  -- ≈ˡ'→≈ˡ (≈lstep p x) = ≈lstep p x
  -- ≈ˡ'→≈ˡ (≈lsym p) = ≈lsym (≈ˡ'→≈ˡ p)
  -- ≈ˡ'→≈ˡ (≈ltrans p p₁) = ≈ltrans (≈ˡ'→≈ˡ p) (≈ˡ'→≈ˡ p₁)

  ≈lrefl : ∀ {t} → t ≈ˡ t
  ≈lrefl {i , x} = ≈lstage i (P̂ i .refl)
    where open ≈.Setoid

  equiv : IsEquivalence _≈ˡ_
  equiv = record
    { refl  = ≈lrefl
    ; sym   = ≈lsym
    ; trans = ≈ltrans
    }
    where open ≈.Setoid

  -- The Colimit Setoid
  Colim : Setoid (ℓI ⊔ ℓB) (ℓI ⊔ ℓ≤ ⊔ ℓB ⊔ ℓB')
  Colim = record
    { Carrier       = Colim₀
    ; _≈_           = _≈ˡ_
    ; isEquivalence = equiv
    }

  -- Cocones for this diagram
  -- Note: Apex lives in the same universe as the Colimit for simplicity here
  record Cocone : Set (lsuc (ℓ≤ ⊔ ℓB' ⊔ ℓB ⊔ ℓI)) where
    field
      Apex     : Setoid (ℓI ⊔ ℓB) (ℓI ⊔ ℓ≤ ⊔ ℓB ⊔ ℓB')
      inj      : ∀ i → ≈.Hom (P̂ i) Apex
      commutes : ∀ {i j} (p : i ≤ j)
               → ≈.Hom≈ (inj i) (inj j ≈.∘ D-mor p)

  open Cocone

  -- The canonical cocone into the colimit
  LimitCocone : Cocone
  LimitCocone = record
    { Apex     = Colim
    ; inj      = λ i → record { to = λ x → i , x ; cong = ≈lstage i }
    ; commutes = λ p {x = x} {y = y} q → ≈ltrans (≈lstage _ q) (≈lstep p y)
    }

  -- Morphisms of cocones
  record ColimMorphism (C C' : Cocone) : Set (ℓI ⊔ ℓ≤ ⊔ ℓB ⊔ ℓB') where
    field
      apexHom  : ≈.Hom (C .Apex) (C' .Apex)
      commutes : ∀ i → ≈.Hom≈ (apexHom ≈.∘ C .inj i) (C' .inj i)

  open ColimMorphism

  -- Universal Property Definition
  record isLimitingCocone (C : Cocone) : Set (lsuc ℓI ⊔ lsuc ℓ≤ ⊔ lsuc ℓB ⊔ lsuc ℓB') where
    field
      mor    : ∀ C' → ColimMorphism C C'
      unique : ∀ C' → (F : ColimMorphism C C') →
                ≈.Hom≈ (F .apexHom) (mor C' .apexHom)

  open isLimitingCocone

  open ≈.Hom

  -- Proof that LimitCocone is limiting
  module IsLimitingCocone (C' : Cocone) where
    module C' = Cocone C'
    module ApexSetoid = ≈.Setoid C'.Apex

    private
      f : ⟨ Colim ⟩ → ⟨ C'.Apex ⟩
      f (i , x) = C'.inj i .to x

    isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y) →
                   f (i , x) ApexSetoid.≈ f (j , y)
    isRespecting (≈lstage i x≈y) = C' .inj i .cong x≈y
    isRespecting (≈lstep p x)    = C'.commutes p (P̂ _ .Setoid.refl)
    isRespecting (≈lsym r)       = ApexSetoid.sym (isRespecting r)
    isRespecting (≈ltrans r s)   =
      ApexSetoid.trans (isRespecting r) (isRespecting s)

    F : ColimMorphism LimitCocone C'
    F .apexHom .to  = f
    F .apexHom .cong = isRespecting
    F .commutes i {x} {y} p =
      (C'.inj (LimitCocone .inj i .to x .proj₁)) .cong p

    unq : (G : ColimMorphism LimitCocone C') →
          ∀ x → G .apexHom .to x ApexSetoid.≈ f x
    unq G (i , x) = G .commutes i ((P̂ _) .Setoid.refl)

  isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
  isLimitingCoconeLimitCocone = record
    { mor    = F
    ; unique = λ C' G x →
        C' .ApexSetoid.trans
          (≈.Hom.cong (G .apexHom) x)
          (G .commutes _ (P̂ _ .Setoid.refl))
    }
    where open IsLimitingCocone
