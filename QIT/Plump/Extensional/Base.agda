open import QIT.Prelude hiding (ℓS; ℓP)

module QIT.Plump.Extensional.Base
  ⦃ pathElim* : PathElim ⦄
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  where

open import QIT.Prop
open import QIT.Logic
import QIT.Container.Base as W
open W hiding (sup)
open import QIT.Setoid

import QIT.Plump.W.Base S P as PlumpW
open import QIT.Relation.Subset

open PlumpW public
  using (Sᶻ ; Pᶻ ; ιₛ ; ∨ₛ ; ⊥ₛ)
  renaming ( Z to Z₀; _≤_ to _≤₀_; _<_ to _<₀_; _≤≥_ to _≤≥₀_
           ; ≤≤ to ≤≤₀ ; ≤< to ≤<₀ ; <≤ to <≤₀
           ; sup≤ to sup≤₀ ; <sup to <sup₀)

open import QIT.Plump.Algebra Sᶻ Pᶻ public

module AlgProperties
  (ZA : Algebra (ℓS ⊔ ℓP))
  where
  open Algebra ZA public

  [_] : Z₀ → Z
  [ W.sup (s , ξ) ] = sup (s , λ i → [ ξ i ])

  <[_] : ∀ {α β} → α <₀ β → [ α ] < [ β ]
  ≤[_] : ∀ {α β} → α ≤₀ β → [ α ] ≤ [ β ]

  <[_] {α} {W.sup (s , ξ)} (<sup₀ i α≤ξi) = <sup i ≤[ α≤ξi ]
  ≤[_] {W.sup (s , ξ)} {β} (sup≤₀ ξ<α) = sup≤ (λ i → <[ ξ<α i ])

  -- Bottom element
  ⊥ᶻ : Z
  ⊥ᶻ = sup (⊥ₛ , λ ())

  -- Binary join: well-defined since α ∨ᶻ γ = sup(∨ₛ, [α,γ]) is
  -- congruent in both arguments by ≤≥-cong.
  _∨ᶻ_ : Z → Z → Z
  α ∨ᶻ β = sup (∨ₛ , ξ)
    where
    ξ : Pᶻ ∨ₛ → Z
    ξ (lift (inj₁ tt)) = α
    ξ (lift (inj₂ tt)) = β

  ∨ᶻ-l : ∀ {α β} → α ≤ (α ∨ᶻ β)
  ∨ᶻ-l {α} {β} = <→≤ (<sup (lift (inj₁ tt)) (≤refl α))

  ∨ᶻ-r : ∀ {α β} → β ≤ (α ∨ᶻ β)
  ∨ᶻ-r {α} {β} = <→≤ (<sup (lift (inj₂ tt)) (≤refl β))

  -- Successor: well-defined since sucᶻ α = sup(∨ₛ, λ _ → α) is
  -- congruent w.r.t. ≤≥ by ≤≥-cong.
  suc : Z → Z
  suc α = α ∨ᶻ α

  -- Embedding of base trees
  ιᶻ : W S P → Z
  ιᶻ (W.sup (s , f)) = sup ((ιₛ s) , λ i → ιᶻ (f i))

  -- -----------------------------------------------------------------------
  -- Derived order lemmas involving the lifted constructors
  -- -----------------------------------------------------------------------

  -- Each child of sup(s, f) is strictly below it.
  child≤ : (s : S) (f : P s → Z) (i : P s) → f i ≤ sup (ιₛ s , f)
  child≤ s f i = <→≤ {f i} {sup (ιₛ s , f)} (<sup {ιₛ s} {f} i {f i} (≤refl (f i)))

  -- Congruence: pointwise ≤ implies ≤ on sup.
  ≤cong : (s : S) (μ τ : P s → Z) → (∀ i → μ i ≤ τ i) → sup (ιₛ s , μ) ≤ sup (ιₛ s , τ)
  ≤cong s μ τ r = sup≤ {ιₛ s} {μ} {sup (ιₛ s , τ)} (λ i → <sup {ιₛ s} {τ} i {μ i} (r i))

  -- α < suc α (the successor is strictly above α).
  <sucᶻ : ∀ α → α < suc α
  <sucᶻ α = <sup (lift (inj₁ tt)) (≤refl α)

  -- Helper: α is strictly below any sup node with shape s when P s is inhabited.
  <supᶻ : ∀ {s : S} (α : Z) → ∥ P s ∥ → α < sup (ιₛ s , λ _ → α)
  <supᶻ {s} α ∣ i ∣ = <sup {ιₛ s} {λ _ → α} i {α} (≤refl α)

  -- -----------------------------------------------------------------------
  -- Preorder structure on Z
  -- -----------------------------------------------------------------------

  open import QIT.Relation.Binary using (IsPreorder; Preorder; WellFounded; Acc; WfRec; acc)

  isPreorder-≤ : IsPreorder _≤_
  isPreorder-≤ = record
    { refl  = λ {x} → ≤refl x
    ; trans = λ {x} {y} {z} p q → ≤≤ {x} {y} {z} q p }

  ≤p : Preorder Z _
  ≤p = _≤_ , isPreorder-≤

  -- Lift the order to the base W-type T via the abstract Z.
  -- These differ from the same-named definitions in QIT.Relation.Plump, which
  -- use the concrete W-type Z₀; here α ranges over the abstract ordinals Z.
  _<ᵀ_ : W S P → Z → Prop (ℓS ⊔ ℓP)
  t <ᵀ α = ιᶻ t < α

  _≤ᵀ_ : W S P → Z → Prop (ℓS ⊔ ℓP)
  t ≤ᵀ α = ιᶻ t ≤ α

  ↓<_ : Z → Set (ℓS ⊔ ℓP)
  ↓< α = ΣP Z (_< α)
  ↓≤_ : Z → Set (ℓS ⊔ ℓP)
  ↓≤ α = ΣP Z (_≤ α)

  _≤↓<_ : ∀ {α} (β γ : ↓< α) → Prop (ℓS ⊔ ℓP)
  (β , _) ≤↓< (γ , _) = β ≤ γ
  _<↓<_ : ∀ {α} (β γ : ↓< α) → Prop (ℓS ⊔ ℓP)
  (β , _) <↓< (γ , _) = β < γ

  _≤↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop (ℓS ⊔ ℓP)
  (β , _) ≤↓≤ (γ , _) = β ≤ γ
  _<↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop (ℓS ⊔ ℓP)
  (β , _) <↓≤ (γ , _) = β < γ

module Properties
  (ZA : Algebra (ℓS ⊔ ℓP))
  (isInitZA : IsInitialExt ZA)
  where
  open Algebra ZA public
  module isInit = IsInitialExt isInitZA
  isExtZA : IsExtensional ZA
  isExtZA = isInit.ext

  [_] : Z₀ → Z
  [ W.sup (s , ξ) ] = sup (s , λ i → [ ξ i ])

  <[_] : ∀ {α β} → α <₀ β → [ α ] < [ β ]
  ≤[_] : ∀ {α β} → α ≤₀ β → [ α ] ≤ [ β ]

  <[_] {α} {W.sup (s , ξ)} (<sup₀ i α≤ξi) = <sup i ≤[ α≤ξi ]
  ≤[_] {W.sup (s , ξ)} {β} (sup≤₀ ξ<α) = sup≤ (λ i → <[ ξ<α i ])

  -- Bottom element
  ⊥ᶻ : Z
  ⊥ᶻ = sup (⊥ₛ , λ ())

  -- Binary join: well-defined since α ∨ᶻ γ = sup(∨ₛ, [α,γ]) is
  -- congruent in both arguments by ≤≥-cong.
  _∨ᶻ_ : Z → Z → Z
  α ∨ᶻ β = sup (∨ₛ , ξ)
    where
    ξ : Pᶻ ∨ₛ → Z
    ξ (lift (inj₁ tt)) = α
    ξ (lift (inj₂ tt)) = β

  ∨ᶻ-l : ∀ {α β} → α ≤ (α ∨ᶻ β)
  ∨ᶻ-l {α} {β} = <→≤ (<sup (lift (inj₁ tt)) (≤refl α))

  ∨ᶻ-r : ∀ {α β} → β ≤ (α ∨ᶻ β)
  ∨ᶻ-r {α} {β} = <→≤ (<sup (lift (inj₂ tt)) (≤refl β))

  -- Successor: well-defined since sucᶻ α = sup(∨ₛ, λ _ → α) is
  -- congruent w.r.t. ≤≥ by ≤≥-cong.
  suc : Z → Z
  suc α = α ∨ᶻ α

  -- Embedding of base trees
  ιᶻ : W S P → Z
  ιᶻ (W.sup (s , f)) = sup ((ιₛ s) , λ i → ιᶻ (f i))

  -- -----------------------------------------------------------------------
  -- Derived order lemmas involving the lifted constructors
  -- -----------------------------------------------------------------------

  -- Each child of sup(s, f) is strictly below it.
  child≤ : (s : S) (f : P s → Z) (i : P s) → f i ≤ sup (ιₛ s , f)
  child≤ s f i = <→≤ {f i} {sup (ιₛ s , f)} (<sup {ιₛ s} {f} i {f i} (≤refl (f i)))

  -- Congruence: pointwise ≤ implies ≤ on sup.
  ≤cong : (s : S) (μ τ : P s → Z) → (∀ i → μ i ≤ τ i) → sup (ιₛ s , μ) ≤ sup (ιₛ s , τ)
  ≤cong s μ τ r = sup≤ {ιₛ s} {μ} {sup (ιₛ s , τ)} (λ i → <sup {ιₛ s} {τ} i {μ i} (r i))

  -- α < suc α (the successor is strictly above α).
  <sucᶻ : ∀ α → α < suc α
  <sucᶻ α = <sup (lift (inj₁ tt)) (≤refl α)

  -- Helper: α is strictly below any sup node with shape s when P s is inhabited.
  <supᶻ : ∀ {s : S} (α : Z) → ∥ P s ∥ → α < sup (ιₛ s , λ _ → α)
  <supᶻ {s} α ∣ i ∣ = <sup {ιₛ s} {λ _ → α} i {α} (≤refl α)

  -- -----------------------------------------------------------------------
  -- Preorder structure on Z
  -- -----------------------------------------------------------------------

  open import QIT.Relation.Binary using (IsPreorder; Preorder; WellFounded; Acc; WfRec; acc)

  isPreorder-≤ : IsPreorder _≤_
  isPreorder-≤ = record
    { refl  = λ {x} → ≤refl x
    ; trans = λ {x} {y} {z} p q → ≤≤ {x} {y} {z} q p }

  ≤p : Preorder Z _
  ≤p = _≤_ , isPreorder-≤

  -- Lift the order to the base W-type T via the abstract Z.
  -- These differ from the same-named definitions in QIT.Relation.Plump, which
  -- use the concrete W-type Z₀; here α ranges over the abstract ordinals Z.
  _<ᵀ_ : W S P → Z → Prop (ℓS ⊔ ℓP)
  t <ᵀ α = ιᶻ t < α

  _≤ᵀ_ : W S P → Z → Prop (ℓS ⊔ ℓP)
  t ≤ᵀ α = ιᶻ t ≤ α

  ↓<_ : Z → Set (ℓS ⊔ ℓP)
  ↓< α = ΣP Z (_< α)
  ↓≤_ : Z → Set (ℓS ⊔ ℓP)
  ↓≤ α = ΣP Z (_≤ α)

  _≤↓<_ : ∀ {α} (β γ : ↓< α) → Prop (ℓS ⊔ ℓP)
  (β , _) ≤↓< (γ , _) = β ≤ γ
  _<↓<_ : ∀ {α} (β γ : ↓< α) → Prop (ℓS ⊔ ℓP)
  (β , _) <↓< (γ , _) = β < γ

  _≤↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop (ℓS ⊔ ℓP)
  (β , _) ≤↓≤ (γ , _) = β ≤ γ
  _<↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop (ℓS ⊔ ℓP)
  (β , _) <↓≤ (γ , _) = β < γ
