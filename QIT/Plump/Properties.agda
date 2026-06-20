open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
open import QIT.Function.Base
import QIT.Container.Base as W

module QIT.Plump.Properties {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Relation.Subset
import QIT.Plump.W.Base S P as PlumpW

open PlumpW public
  using (Sᶻ ; Pᶻ ; ιˢ ; ∨ˢ ; ⊥ˢ)

open import QIT.Plump.Algebra Sᶻ Pᶻ public

module AlgProperties {ℓA}
  (ZA : Algebra ℓA)
  where
  open Algebra ZA public

  -- Bottom element
  ⊥ᶻ : Z
  ⊥ᶻ = sup (⊥ˢ , λ ())

  -- Binary join: well-defined since α ∨ᶻ γ = sup(∨ˢ, [α,γ]) is
  -- congruent in both arguments by ≤≥-cong.
  _∨ᶻ_ : Z → Z → Z
  α ∨ᶻ β = sup (∨ˢ , ξ)
    where
    ξ : Pᶻ ∨ˢ → Z
    ξ (lift (inj₁ tt)) = α
    ξ (lift (inj₂ tt)) = β

  ∨ᶻ-l : ∀ {α β} → α ≤ (α ∨ᶻ β)
  ∨ᶻ-l {α} {β} = <→≤ (<sup (lift (inj₁ tt)) (≤refl α))

  ∨ᶻ-r : ∀ {α β} → β ≤ (α ∨ᶻ β)
  ∨ᶻ-r {α} {β} = <→≤ (<sup (lift (inj₂ tt)) (≤refl β))

  -- Successor: well-defined since sucᶻ α = sup(∨ˢ, λ _ → α) is
  -- congruent w.r.t. ≤≥ by ≤≥-cong.
  suc : Z → Z
  suc α = α ∨ᶻ α

  -- Embedding of base trees
  ιᶻ : W.W S P → Z
  ιᶻ (W.sup (s , f)) = sup (ιˢ s , λ i → ιᶻ (f i))

  -- -----------------------------------------------------------------------
  -- Derived order lemmas involving the lifted constructors
  -- -----------------------------------------------------------------------

  -- Each child of sup(s, f) is strictly below it.
  child≤ : (s : S) (f : P s → Z) (i : P s) → f i ≤ sup (ιˢ s , f)
  child≤ s f i = <→≤ {f i} {sup (ιˢ s , f)} (<sup {ιˢ s} {f} i {f i} (≤refl (f i)))

  -- Congruence: pointwise ≤ implies ≤ on sup.
  ≤cong : (s : S) (μ τ : P s → Z) → (∀ i → μ i ≤ τ i) → sup (ιˢ s , μ) ≤ sup (ιˢ s , τ)
  ≤cong s μ τ r = sup≤ {ιˢ s} {μ} {sup (ιˢ s , τ)} (λ i → <sup {ιˢ s} {τ} i {μ i} (r i))

  -- α < suc α (the successor is strictly above α).
  <sucᶻ : ∀ α → α < suc α
  <sucᶻ α = <sup (lift (inj₁ tt)) (≤refl α)

  -- Helper: α is strictly below any sup node with shape s when P s is inhabited.
  <supᶻ : ∀ {s : S} (α : Z) → ∥ P s ∥ → α < sup (ιˢ s , λ _ → α)
  <supᶻ {s} α ∣ i ∣ = <sup {ιˢ s} {λ _ → α} i {α} (≤refl α)

  -- -----------------------------------------------------------------------
  -- Preorder structure on Z
  -- -----------------------------------------------------------------------

  open import QIT.Relation.Binary using (IsPreorder; Preorder)

  isPreorder-≤ : IsPreorder _≤_
  isPreorder-≤ = record
    { refl  = λ {x} → ≤refl x
    ; trans = λ {x} {y} {z} p q → ≤≤ {x} {y} {z} q p }

  ≤p : Preorder Z _
  ≤p = _≤_ , isPreorder-≤

  -- Lift the order to the base W-type T via the abstract Z.
  _<ᵀ_ : W.W S P → Z → Prop ℓA
  t <ᵀ α = ιᶻ t < α

  _≤ᵀ_ : W.W S P → Z → Prop ℓA
  t ≤ᵀ α = ιᶻ t ≤ α

  ↓<_ : Z → Set ℓA
  ↓< α = ΣP Z (_< α)

  ↓≤_ : Z → Set ℓA
  ↓≤ α = ΣP Z (_≤ α)

  _≤↓<_ : ∀ {α} (β γ : ↓< α) → Prop ℓA
  (β , _) ≤↓< (γ , _) = β ≤ γ

  _<↓<_ : ∀ {α} (β γ : ↓< α) → Prop ℓA
  (β , _) <↓< (γ , _) = β < γ

  _≤↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop ℓA
  (β , _) ≤↓≤ (γ , _) = β ≤ γ

  _<↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop ℓA
  (β , _) <↓≤ (γ , _) = β < γ

  ↓_ : Z → Set ℓA
  ↓_ = ↓≤_

  inc↓ : ∀ {α β} → α ≤ β → ↓ α → ↓ β
  inc↓ p γ = γ .fst , ≤≤ p (γ .snd)

  open import QIT.Category.Preorder Z ≤p
  open import QIT.Category.Equivalence

  record IsRegular (κ : Z) : Prop ℓA where
    field
      regular : ∀ α → α < κ → Equivalence (PreorderCat↓ α) (PreorderCat↓ κ) → ⊥p
