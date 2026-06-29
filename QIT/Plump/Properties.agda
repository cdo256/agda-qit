open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
open import QIT.Function.Base
import QIT.Container.Base as W

module QIT.Plump.Properties
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Relation.Subset

open import QIT.Plump.Algebra public

freePlumpAlgebra
  : ∀ {ℓS ℓP ℓX ℓ< ℓ≤} (S : Set ℓS) (P : S → Set ℓP)
  → (X : Set ℓX) (_<₀_ : X → X → Prop ℓ<) (_≤₀_ : X → X → Prop ℓ≤)
  → Algebra S P (ℓX ⊔ ℓS ⊔ ℓP ⊔ ℓ< ⊔ ℓ≤) 
freePlumpAlgebra {ℓS} {ℓP} {ℓX} {ℓ<} {ℓ≤} S P X _<₀_ _≤₀_ = record
  { Z = Z
  ; sup = sup
  ; _<_ = _<_
  ; _≤_ = _≤_
  ; sup≤ = sup≤
  ; <sup = <sup
  ; ≤≤ = ≤≤
  ; ≤< = ≤<
  ; <≤ = <≤
  ; << = <<
  ; <→≤ = <→≤
  ; ≤refl = ≤refl
  }
  where 
  ℓAlg = ℓX ⊔ ℓS ⊔ ℓP ⊔ ℓ< ⊔ ℓ≤
  data Z : Set ℓAlg where 
    ι : X → Z
    sup : Σ S (λ s → P s → Z) → Z 
  data _<_ : Z → Z → Prop ℓAlg
  data _≤_ : Z → Z → Prop ℓAlg
  data _<_ where
    ι< : ∀ {α β} → α <₀ β → ι α < ι β
    <sup : {s : S} {f : P s → Z}
          → (i : P s) → {α : Z}
          → α ≤ f i
          → α < sup (s , f)
    ≤< : {α β γ : Z} → β ≤ γ → α < β → α < γ
    <≤ : {α β γ : Z} → β < γ → α ≤ β → α < γ
    << : {α β γ : Z} → β < γ → α < β → α < γ
  data _≤_ where
    ι≤ : ∀ {α β} → α ≤₀ β → ι α ≤ ι β
    sup≤ : {s : S} {f : P s → Z} {α : Z}
          → (∀ i → f i < α)
          → sup (s , f) ≤ α
    ≤refl : ∀ α → α ≤ α
    ≤≤ : {α β γ : Z} → β ≤ γ → α ≤ β → α ≤ γ
    <→≤ : {α β : Z} → α < β → α ≤ β


union : ∀ {ℓS₁ ℓS₂ ℓP₁ ℓA₁ ℓA₂} {S₁ : Set ℓS₁} {S₂ : Set ℓS₂} {P₁ : S₁ → Set ℓP₁} {P₂ : S₂ → Set ℓP₁}
      → Algebra S₁ P₁ ℓA₁ → Algebra S₂ P₂ ℓA₂
      → Algebra (S₁ ⊎ S₂) ⊎.[ P₁ , P₂ ] (ℓS₁ ⊔ ℓS₂ ⊔ ℓP₁ ⊔ ℓA₁ ⊔ ℓA₂)
union {ℓS₁} {ℓS₂} {ℓP₁} {ℓA₁} {ℓA₂} {S₁} {S₂} {P₁} {P₂} A₁ A₂ = freePlumpAlgebra S P Z _<_ _≤_
  where
  module A₁ = Algebra A₁
  module A₂ = Algebra A₂
  S : Set _
  S = S₁ ⊎ S₂
  P : S → Set _
  P = ⊎.[ P₁ , P₂ ]
  data Z : Set (ℓS₁ ⊔ ℓS₂ ⊔ ℓP₁ ⊔ ℓA₁ ⊔ ℓA₂) where 
    ι₁ : A₁.Z → Z
    ι₂ : A₂.Z → Z
  data _<_ : Z → Z → Prop (ℓS₁ ⊔ ℓS₂ ⊔ ℓP₁ ⊔ ℓA₁ ⊔ ℓA₂) where
    ι<₁ : ∀ {α β} → α A₁.< β → ι₁ α < ι₁ β
    ι<₂ : ∀ {α β} → α A₂.< β → ι₂ α < ι₂ β
  data _≤_ : Z → Z → Prop (ℓS₁ ⊔ ℓS₂ ⊔ ℓP₁ ⊔ ℓA₁ ⊔ ℓA₂) where
    ι≤₁ : ∀ {α β} → α A₁.≤ β → ι₁ α ≤ ι₁ β
    ι≤₂ : ∀ {α β} → α A₂.≤ β → ι₂ α ≤ ι₂ β

module AlgProperties
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  {ℓA} (ZA : Algebra S P ℓA)
  where
  open Algebra ZA public



  -- -- Bottom element
  -- ⊥ᶻ : Z
  -- ⊥ᶻ = sup (⊥ₛ , λ ())

  -- -- Binary join: well-defined since α ∨ᶻ γ = sup(∨ₛ, [α,γ]) is
  -- -- congruent in both arguments by ≤≥-cong.
  -- _∨ᶻ_ : Z → Z → Z
  -- α ∨ᶻ β = sup (∨ₛ , ξ)
  --   where
  --   ξ : Pᶻ ∨ₛ → Z
  --   ξ (lift (inj₁ tt)) = α
  --   ξ (lift (inj₂ tt)) = β

  -- ∨ᶻ-l : ∀ {α β} → α ≤ (α ∨ᶻ β)
  -- ∨ᶻ-l {α} {β} = <→≤ (<sup (lift (inj₁ tt)) (≤refl α))

  -- ∨ᶻ-r : ∀ {α β} → β ≤ (α ∨ᶻ β)
  -- ∨ᶻ-r {α} {β} = <→≤ (<sup (lift (inj₂ tt)) (≤refl β))

  -- -- Successor: well-defined since sucᶻ α = sup(∨ₛ, λ _ → α) is
  -- -- congruent w.r.t. ≤≥ by ≤≥-cong.
  -- suc : Z → Z
  -- suc α = α ∨ᶻ α

  -- -- Embedding of base trees
  -- ιᶻ : W.W S P → Z
  -- ιᶻ (W.sup (s , f)) = sup (ιₛ s , λ i → ιᶻ (f i))

  -- -----------------------------------------------------------------------
  -- Derived order lemmas involving the lifted constructors
  -- -----------------------------------------------------------------------

  -- Each child of sup(s, f) is strictly below it.
  child≤ : (s : S) (f : P s → Z) (i : P s) → f i ≤ sup (s , f)
  child≤ s f i = <→≤ {f i} {sup (s , f)} (<sup {s} {f} i {f i} (≤refl (f i)))

  -- Congruence: pointwise ≤ implies ≤ on sup.
  ≤cong : (s : S) (μ τ : P s → Z) → (∀ i → μ i ≤ τ i) → sup (s , μ) ≤ sup (s , τ)
  ≤cong s μ τ r = sup≤ {s} {μ} {sup (s , τ)} (λ i → <sup {s} {τ} i {μ i} (r i))

  -- -- α < suc α (the successor is strictly above α).
  -- <sucᶻ : ∀ α → α < suc α
  -- <sucᶻ α = <sup (lift (inj₁ tt)) (≤refl α)

  -- Helper: α is strictly below any sup node with shape s when P s is inhabited.
  <supᶻ : ∀ {s : S} (α : Z) → ∥ P s ∥ → α < sup (s , λ _ → α)
  <supᶻ {s} α ∣ i ∣ = <sup {s} {λ _ → α} i {α} (≤refl α)

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

  -- -- Lift the order to the base W-type T via the abstract Z.
  -- _<ᵀ_ : W.W S P → Z → Prop ℓA
  -- t <ᵀ α = ιᶻ t < α

  -- _≤ᵀ_ : W.W S P → Z → Prop ℓA
  -- t ≤ᵀ α = ιᶻ t ≤ α

  -- ↓<_ : Z → Set ℓA
  -- ↓< α = ΣP Z (_< α)

  -- ↓≤_ : Z → Set ℓA
  -- ↓≤ α = ΣP Z (_≤ α)

  -- _≤↓<_ : ∀ {α} (β γ : ↓< α) → Prop ℓA
  -- (β , _) ≤↓< (γ , _) = β ≤ γ

  -- _<↓<_ : ∀ {α} (β γ : ↓< α) → Prop ℓA
  -- (β , _) <↓< (γ , _) = β < γ

  -- _≤↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop ℓA
  -- (β , _) ≤↓≤ (γ , _) = β ≤ γ

  -- _<↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop ℓA
  -- (β , _) <↓≤ (γ , _) = β < γ

  -- ↓_ : Z → Set ℓA
  -- ↓_ = ↓≤_

  -- inc↓ : ∀ {α β} → α ≤ β → ↓ α → ↓ β
  -- inc↓ p γ = γ .fst , ≤≤ p (γ .snd)

  -- open import QIT.Category.Preorder Z ≤p
  -- open import QIT.Category.Equivalence

  -- record IsRegular (κ : Z) : Prop ℓA where
  --   field
  --     regular : ∀ α → α < κ → Equivalence (PreorderCat↓ α) (PreorderCat↓ κ) → ⊥
