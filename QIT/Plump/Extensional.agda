module QIT.Plump.Extensional {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
import QIT.Container.Base as W
open W hiding (sup)
open import QIT.Setoid

import QIT.Relation.Plump S P as Plump
open import QIT.Relation.Subset

open Plump public
  using (Sᶻ ; Pᶻ ; ιˢ ; ∨ˢ ; ⊥ˢ)
  renaming ( Z to Z₀; _≤_ to _≤₀_; _<_ to _<₀_; _≤≥_ to _≤≥₀_
           ; ≤≤ to ≤≤₀ ; ≤< to ≤<₀ ; <≤ to <≤₀
           ; sup≤ to sup≤₀ ; <sup to <sup₀)

open import QIT.Plump.Algebra Sᶻ Pᶻ public

record InitialAlgebra (ℓX : Level)
  : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓX) where
  field
    Zᴬ : Algebra (ℓS ⊔ ℓP)
    recʰ : (Xᴬ : Algebra ℓX) → Hom Zᴬ Xᴬ
    recʰ-unique : (Xᴬ : Algebra ℓX)
                → (fʰ : Hom Zᴬ Xᴬ) → recʰ Xᴬ ≈ʰ fʰ

  open Algebra Zᴬ public
  module _ (Xᴬ : Algebra ℓX) where
    open Hom (recʰ Xᴬ) public
      renaming ( Zʰ to rec ; supʰ to rec-β
              ; <ʰ to rec< ; ≤ʰ to rec≤ )
    -- {-# REWRITE rec-β #-}
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

    -- Set-valued structural eliminator / well-founded recursion.
    -- To compute B α for every ordinal α, it suffices to show how to
    -- compute B (sup (s , ξ)) given the values B (ξ i) for all children.
    -- This is the counterpart of elim≤/elim< for Set-valued predicates.
    ind : ∀ {ℓB} (B : Z → Set ℓB)
        → ({s : Sᶻ} {ξ : Pᶻ s → Z}
          → (∀ i → B (ξ i))
          → B (sup (s , ξ)))
        → ∀ α → B α
    ind-β : ∀ {ℓB} (B : Z → Set ℓB)
            (step : {s : Sᶻ} {ξ : Pᶻ s → Z} → (∀ i → B (ξ i)) → B (sup (s , ξ)))
            (s : Sᶻ) (ξ : Pᶻ s → Z)
          → ind B step (sup (s , ξ)) ≡ step (λ i → ind B step (ξ i))
  -- {-# REWRITE ind-β #-}

  postulate
    -- minimum
    _∧ᶻ_ : Z → Z → Z 
    ∧≤₁ : ∀ {α β} → (α ∧ᶻ β) ≤ α
    ∧≤₂ : ∀ {α β} → (α ∧ᶻ β) ≤ β
    ∧-lim : ∀ {α β γ} → γ ≤ α → γ ≤ β → γ ≤ (α ∧ᶻ β)

  -- Non-dependent recursion: fold over the tree shape.
  -- step receives the shape s, the child ordinals ξ, and the
  -- recursively-computed results for each child.
  fold : ∀ {ℓB} {B : Set ℓB}
      → ((s : Sᶻ) (ξ : Pᶻ s → Z) → (Pᶻ s → B) → B)
      → Z → B
  fold step = ind _ (λ {s} {ξ} ih → step s ξ ih)

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
