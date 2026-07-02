open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
open import QIT.Function.Base
import QIT.Container.Base as W

open import QIT.Relation.Subset
open import QIT.Plump.Algebra

module QIT.Plump.Properties
  ⦃ pathElim* : PathElim ⦄
  {ℓS ℓP ℓZ ℓ< ℓ≤} {S : Set ℓS} {P : S → Set ℓP}
  (Zᴬ : PlumpAlgebra S P ℓZ ℓ< ℓ≤)
  where

open PlumpAlgebra Zᴬ public

private T = W.W S P

ιᶻ : T → Z
ιᶻ (W.sup (s , f)) = sup (s , λ i → ιᶻ (f i))

sucᶻ : Z → Z
sucᶻ α = α ∨ᶻ α

sup≤sup : ∀ {s f g} (r : ∀ i → f i ≤ g i) → sup (s , f) ≤ sup (s , g)
sup≤sup r = sup≤ (λ i → <sup i (r i))

≡→≤ : ∀ {α β} → α ≡ β → α ≤ β
≡→≤ {α} {α} ≡.refl = ≤refl α

-- Helper: for any x and any inhabited P s, x is strictly below the
-- one-node tree with shape ιˢ s and all children equal to x.
-- This is used when we need "at least one branch exists" to witness <.
<supᶻ : ∀ {s} x → ∥ P s ∥ → x < sup (s , λ _ → x)
<supᶻ x ∣ α ∣ = <sup α (≤refl x)

-- Each child of sup(s, f) is strictly below it.
child≤ : (s : S) (f : P s → Z) (i : P s) → f i ≤ sup (s , f)
child≤ s f i = <→≤ {f i} {sup (s , f)} (<sup {s} {f} i {f i} (≤refl (f i)))

-- Congruence: pointwise ≤ implies ≤ on sup.
≤cong : (s : S) (μ τ : P s → Z) → (∀ i → μ i ≤ τ i) → sup (s , μ) ≤ sup (s , τ)
≤cong s μ τ r = sup≤ {s} {μ} {sup (s , τ)} (λ i → <sup {s} {τ} i {μ i} (r i))

-- α < suc α (the successor is strictly above α).
<sucᶻ : ∀ α → α < sucᶻ α
<sucᶻ α = ∨ᶻ-l<

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
_<ᵀ_ : W.W S P → Z → Prop _
t <ᵀ α = ιᶻ t < α

_≤ᵀ_ : W.W S P → Z → Prop _
t ≤ᵀ α = ιᶻ t ≤ α

↓<_ : Z → Set _
↓< α = ΣP Z (_< α)

↓≤_ : Z → Set _
↓≤ α = ΣP Z (_≤ α)

_≤↓<_ : ∀ {α} (β γ : ↓< α) → Prop _
(β , _) ≤↓< (γ , _) = β ≤ γ

_<↓<_ : ∀ {α} (β γ : ↓< α) → Prop _
(β , _) <↓< (γ , _) = β < γ

_≤↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop _
(β , _) ≤↓≤ (γ , _) = β ≤ γ

_<↓≤_ : ∀ {α} (β γ : ↓≤ α) → Prop _
(β , _) <↓≤ (γ , _) = β < γ

↓_ : Z → Set _
↓_ = ↓≤_

inc↓ : ∀ {α β} → α ≤ β → ↓ α → ↓ β
inc↓ p γ = γ .fst , ≤≤ p (γ .snd)

open import QIT.Category.Preorder Z ≤p
open import QIT.Category.Equivalence

record IsRegular (κ : Z) : Prop (ℓZ ⊔ ℓ< ⊔ ℓ≤) where
  field
    regular : ∀ α → α < κ → Equivalence (PreorderCat↓ α) (PreorderCat↓ κ) → ⊥
