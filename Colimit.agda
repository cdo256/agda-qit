{-# OPTIONS --type-in-type #-}

open import Prelude
open import Equivalence
open import Setoid
open import Data.Product

module Colimit {ℓI} {ℓ≤} {ℓB} {ℓB'}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  where

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

record Diagram : Set (ℓ≤ ⊔ lsuc ℓB ⊔ lsuc ℓB') where
  module ≤ = IsPreorder (≤p .proj₂)
  _≤_ : Rel I ℓ≤
  _≤_ = ≤p .proj₁

  field
    D-ob : ∀ (i : I) → Setoid ℓB ℓB'
    D-mor : ∀ {i j} → (p : i ≤ j) → ≈.Hom (D-ob i) (D-ob j)
    D-id : ∀ {i : I}
         → ≈.Hom≈ (D-mor (≤.refl))
                  (≈.idHom {S = D-ob i})
    D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
           → ≈.Hom≈ (D-mor (≤.trans p q))
                    (D-mor q ≈.∘ D-mor p)

module Colim (P : Diagram) where
  open Diagram P renaming (D-ob to P̂)

  private 
    Pf : ∀ {i j} (p : i ≤ j) → (⟨ P̂ i ⟩ → ⟨ P̂ j ⟩)
    Pf p = ⟦_⟧
      where open ≈.Hom (D-mor p)

  open import Data.Product

  -- The carrier of the colimit (Sigma type)
  Colim₀ : Set (ℓI ⊔ ℓB)
  Colim₀ = Σ[ i ∈ I ] ⟨ P̂ i ⟩

  -- The equivalence relation generating the colimit
  data _≈ˡ_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓB ⊔ ℓB') where
    ≈lstage : ∀ i → {x x' : ⟨ P̂ i ⟩} → P̂ i [ x ≈ x' ] → (i , x) ≈ˡ (i , x')
    ≈lstep  : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → (i , x) ≈ˡ (j , Pf p x)
    ≈lsym   : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
    ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u

  equiv : IsEquivalence _≈ˡ_
  equiv = record
    { refl  = λ { {(i , x)} → ≈lstage i (P̂ i .refl) }
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
    ; inj      = λ i → record { ⟦_⟧ = λ x → i , x ; cong = ≈lstage i }
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
  -- module ≈ = Setoid

  -- Proof that LimitCocone is limiting
  module IsLimitingCocone (C' : Cocone) where
    module C' = Cocone C'
    module ApexSetoid = ≈.Setoid C'.Apex

    private
      f : ⟨ Colim ⟩ → ⟨ C'.Apex ⟩
      f (i , x) = C'.inj i .⟦_⟧ x

    isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y) →
                   f (i , x) ApexSetoid.≈ f (j , y)
    isRespecting (≈lstage i x≈y) = C' .inj i .cong x≈y
    isRespecting (≈lstep p x)    = C'.commutes p (P̂ _ .Setoid.refl)
    isRespecting (≈lsym r)       = ApexSetoid.sym (isRespecting r)
    isRespecting (≈ltrans r s)   =
      ApexSetoid.trans (isRespecting r) (isRespecting s)

    F : ColimMorphism LimitCocone C'
    F .apexHom .⟦_⟧  = f
    F .apexHom .cong = isRespecting
    F .commutes i {x} {y} p =
      (C'.inj (LimitCocone .inj i .⟦_⟧ x .proj₁)) .cong p

    unq : (G : ColimMorphism LimitCocone C') →
          ∀ x → G .apexHom .⟦_⟧ x ApexSetoid.≈ f x
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
