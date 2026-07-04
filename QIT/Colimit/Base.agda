open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Set.Base
open import QIT.Functor.Base
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Relation.SetQuotient

module QIT.Colimit.Base
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ fe* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  (ℓD ℓD' : Level)
  (P : Functor (PreorderCat I ≤p) (SetCat (ℓD ⊔ ℓD')))
 where

  open import QIT.Setoid
  open import QIT.Setoid.Quotient

  private
    module ≤ = IsPreorder (≤p .proj₂)
    _≤_ : BinaryRel I ℓ≤
    _≤_ = ≤p .proj₁

  open Functor P using () renaming (ob to P̂)
  module P = Functor P

  Pf : ∀ {i j} (p : i ≤ j) → (P̂ i → P̂ j)
  Pf p = P.hom (box p)

  Colim₀ : Set (ℓI ⊔ ℓD ⊔ ℓD')
  Colim₀ = Σ I P̂

  data _≈ˡ_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓD ⊔ ℓD') where
    ≈lstage : ∀ i → {x x' : P̂ i} → x ≡ x'
            → (i , x) ≈ˡ (i , x')
    ≈lstep  : ∀ {i j} (p : i ≤ j) (x : P̂ i) → (i , x) ≈ˡ (j , Pf p x)
    ≈lsym   : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
    ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u

  recˡ : ∀ {ℓ} (C : ∀ {s t} → s ≈ˡ t → Prop ℓ)
       → (c-stage : ∀ i {x x'} (e : x ≡ x') → C (≈lstage i e))
       → (c-step  : ∀ {i j} (p : i ≤ j) (x : P̂ i) → C (≈lstep p x))
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

  ≈lrefl : ∀ {t} → t ≈ˡ t
  ≈lrefl {i , x} = ≈lstage i ≡.refl
    where open ≈.Setoid

  equiv : IsEquivalence _≈ˡ_
  equiv = record
    { refl  = ≈lrefl
    ; sym   = ≈lsym
    ; trans = ≈ltrans
    }
    where open ≈.Setoid

  Colim : Setoid (ℓI ⊔ ℓD ⊔ ℓD') (ℓI ⊔ ℓ≤ ⊔ ℓD ⊔ ℓD')
  Colim = record
    { Carrier       = Colim₀
    ; _≈_           = _≈ˡ_
    ; isEquivalence = equiv
    }

  Colim/ : Set (ℓI ⊔ ℓD ⊔ ℓD' ⊔ ℓ≤)
  Colim/ = Colim /≈
