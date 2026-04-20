module QIT.Examples.Plump.Postulated {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
import QIT.Container.Base as W
open W hiding (sup)
open import QIT.Setoid

import QIT.Relation.Plump S P as Plump

open Plump public
  using (Sᶻ ; Pᶻ ; ιˢ ; ∨ˢ ; ⊥ˢ)
  renaming ( Z to Z₀; _≤_ to _≤₀_; _<_ to _<₀_; _≤≥_ to _≤≥₀_
           ; ≤≤ to ≤≤₀ ; ≤< to ≤<₀ ; <≤ to <≤₀
           ; sup≤ to sup≤₀ ; <sup to <sup₀)

open import QIT.Examples.Plump.Algebra Sᶻ Pᶻ

postulate
  Zᴬ : Algebra (ℓS ⊔ ℓP)
  recʰ : ∀ {ℓX} (Xᴬ : Algebra ℓX) → Hom Zᴬ Xᴬ
  recʰ-unique : ∀ {ℓX} (Xᴬ : Algebra ℓX)
              → (fʰ : Hom Zᴬ Xᴬ) → recʰ Xᴬ ≈ʰ fʰ

open Algebra Zᴬ public
module _ {ℓX} (Xᴬ : Algebra ℓX) where
  open Hom (recʰ Xᴬ) public
    renaming ( Zʰ to rec ; supʰ to rec-β
             ; <ʰ to rec< ; ≤ʰ to rec≤ )
  {-# REWRITE rec-β #-}
  module _ (fʰ : Hom Zᴬ Xᴬ) where
    open _≈ʰ_ (recʰ-unique Xᴬ fʰ)
      renaming (≈Zʰ to rec-unique)

[_] : Z₀ → Z
[ W.sup (s , ξ) ] = sup (s , λ i → [ ξ i ])

postulate
  elim≤ : ∀ {ℓB} (B : Z → Prop ℓB) {β : Z}
        → ({s : Sᶻ} {ξ : Pᶻ s → Z}
          → (ξi<β : ∀ i → ξ i < β)
          → B (sup (s , ξ)))
        → (∀ {α} → α ≤ β → B α)
  elim< : ∀ {ℓB} (B : Z → Prop ℓB) {α : Z}
        → ({s : Sᶻ} {ξ : Pᶻ s → Z}
          → (i : Pᶻ s) → α ≤ ξ i
          → B (sup (s , ξ)))
        → (∀ {β} → α < β → B β)

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
