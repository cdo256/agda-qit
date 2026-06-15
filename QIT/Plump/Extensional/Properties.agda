open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Properties
open import QIT.Prop.Logic
import QIT.Container.Base as W
open W hiding (sup)
open import QIT.Setoid

module QIT.Plump.Extensional.Properties {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
import QIT.Container.Base as W
open import QIT.Setoid

import QIT.Plump.W.Base S P as Plump
open import QIT.Relation.Subset

open Plump public
  using (Sᶻ ; Pᶻ ; ιˢ ; ∨ˢ ; ⊥ˢ)
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
  ιᶻ : W S P → Z
  ιᶻ (W.sup (s , f)) = sup ((ιˢ s) , λ i → ιᶻ (f i))

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

  
-- open import QIT.Function.Base
-- open import QIT.Relation.Subset
-- open import QIT.Relation.Binary
-- open import QIT.Category.Preorder Z ≤p

-- ↓_ = ↓≤_

-- inc↓ : ∀ {α β} → α ≤ β → ↓ α → ↓ β 
-- inc↓ p γ = γ .fst , ≤≤ p (γ .snd)

-- CanonicalSurjection : ∀ {α β} → α ≤ β → ↓ β → ↓ α
-- CanonicalSurjection {α} p (γ , γ≤β) = (α ∧ᶻ γ) , ∧≤₁

-- -- swan2022 4.1
-- isSurjectionCanonicalSurjection : ∀ {α β} → (p : α ≤ β) → Surjective (CanonicalSurjection p)
-- isSurjectionCanonicalSurjection {α} {β} p (γ , γ≤α) =
--   ∣ inc↓ p (γ , γ≤α) , ΣP≡ _ _ q ∣
--   where
--   q : α ∧ᶻ γ ≡ γ
--   q = ≤antisym ∧≤₂ (∧-lim γ≤α (≤refl γ))

-- -- Too strong constructively. Use Acc instead?
-- record IsWellOrder {ℓA ℓR} (A : Set ℓA) (R : A → A → Prop ℓR) : Prop (lsuc ℓS ⊔ ℓA ⊔ ℓR) where
--   field
--     minSet : ∀ (S : A → Prop ℓS) → ∃ S
--            → ∃ {A = ΣP A S} λ (x , xs) → ∀ ((y , ys) : ΣP A S) → R y x 
     

-- open import QIT.Category.Equivalence
-- record IsRegular (κ : Z) : Prop (ℓS ⊔ ℓP) where
--   field
--     regular : ∀ α → α < κ → Equivalence (PreorderCat↓ α) (PreorderCat↓ κ) → ⊥p

