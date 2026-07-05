open import QIT.Prelude
open import QIT.Prop hiding (⊥; _∨_)
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.Algebra
  ⦃ pathElim* : PathElim ⦄       
  where

record PlumpAlgebra
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where

  infix 4 _≤_ _<_
  infixl 10 _∨ᶻ_

  private
    T = W.W S P

  field
    Z : Set (ℓS ⊔ ℓP)
    sup : Σ S (λ s → P s → Z) → Z
    _<_ : Z → Z → Prop (ℓS ⊔ ℓP)
    _≤_ : Z → Z → Prop (ℓS ⊔ ℓP)

    sup≤ : {s : S} {f : P s → Z} {α : Z}
          → (∀ i → f i < α)
          → sup (s , f) ≤ α
    <sup : {s : S} {f : P s → Z}
          → (i : P s) → {α : Z}
          → α ≤ f i
          → α < sup (s , f)

    ≤≤ : {α β γ : Z} → β ≤ γ → α ≤ β → α ≤ γ
    ≤< : {α β γ : Z} → β ≤ γ → α < β → α < γ
    <≤ : {α β γ : Z} → β < γ → α ≤ β → α < γ
    << : {α β γ : Z} → β < γ → α < β → α < γ
    <→≤ : {α β : Z} → α < β → α ≤ β

    ≤refl : ∀ α → α ≤ α

    _∨ᶻ_ : Z → Z → Z
    ∨ᶻ-l< : ∀ {α β} → α < (α ∨ᶻ β)
    ∨ᶻ-r< : ∀ {α β} → β < (α ∨ᶻ β)
    ∨ᶻ≤ : ∀ {α β γ} → α < γ → β < γ → (α ∨ᶻ β) ≤ γ
    ∨ᶻ-flip : ∀ {α β} → (β ∨ᶻ α) ≤ (α ∨ᶻ β)

    ⊥ᶻ : Z
    ⊥ᶻ≤ : ∀ {α} → ⊥ᶻ ≤ α

    -- iswf< : WellFounded _<_

record ExtensionalPlumpAlgebra
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    Zᴬ : PlumpAlgebra S P

  open PlumpAlgebra Zᴬ public

  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

  -- [_]ᶻ : Z₀.Z → Z
  -- [ W.sup (Z₀.⊥ₛ , f) ]ᶻ = ⊥ᶻ
  -- [ W.sup (Z₀.∨ₛ , f) ]ᶻ =
  --      [ f (inj₁ tt*) ]ᶻ
  --   ∨ᶻ [ f (inj₂ tt*) ]ᶻ
  -- [ W.sup (Z₀.ιₛ s , f) ]ᶻ =
  --   sup (s , λ i → [ f i ]ᶻ)
  -- ιᶻ-factors : ∀ x → [ Z₀Prop.ιᶻ x ]ᶻ ≡ ιᶻ x
  -- ιᶻ-factors (W.sup (s , f)) =
  --   ≡.cong (λ ○ → sup (s , ○))
  --          (funExt λ i → ιᶻ-factors (f i))
  -- ≤[_]ᶻ : ∀ {α β : Z₀.Z}
  --       → α Z₀.≤ β → [ α ]ᶻ ≤ [ β ]ᶻ
  -- <[_]ᶻ : ∀ {α β : Z₀.Z}
  --       → α Z₀.< β → [ α ]ᶻ < [ β ]ᶻ
  -- <[_]ᶻ {α} {W.sup (Z₀.⊥ₛ , ξ)} (Z₀.<sup () α≤ξi)
  -- <[_]ᶻ {α} {W.sup (Z₀.∨ₛ , ξ)} (Z₀.<sup (inj₁ tt*) α≤ξ₁) =
  --   <≤ ∨ᶻ-l< ≤[ α≤ξ₁ ]ᶻ
  -- <[_]ᶻ {α} {W.sup (Z₀.∨ₛ , ξ)} (Z₀.<sup (inj₂ tt*) α≤ξ₂) =
  --   <≤ ∨ᶻ-r< ≤[ α≤ξ₂ ]ᶻ
  -- <[_]ᶻ {α} {W.sup (Z₀.ιₛ s , ξ)} (Z₀.<sup i α≤ξi) =
  --   <sup i ≤[ α≤ξi ]ᶻ
  -- ≤[_]ᶻ {W.sup (Z₀.⊥ₛ , ξ)} {β} _ = ⊥ᶻ≤
  -- ≤[_]ᶻ {W.sup (Z₀.∨ₛ , ξ)} {β} (Z₀.sup≤ ξ<β) =
  --   ∨ᶻ≤ <[ ξ<β (inj₁ tt*) ]ᶻ <[ ξ<β (inj₂ tt*) ]ᶻ
  -- ≤[_]ᶻ {W.sup (Z₀.ιₛ s , ξ)} {β} (Z₀.sup≤ ξ<β) =
  --   sup≤ (λ i → <[ ξ<β i ]ᶻ)

  -- ιᶻ≤ιᶻ : ∀ x y
  --   → Z₀Prop.ιᶻ x Z₀.≤ Z₀Prop.ιᶻ y 
  --   → ιᶻ x ≤ ιᶻ y
  -- ιᶻ≤ιᶻ x y p =
  --   ≡.substp₂ _≤_
  --     (ιᶻ-factors x)
  --     (ιᶻ-factors y)
  --     ≤[ p ]ᶻ

  -- ιᶻ≤≥ιᶻ : ∀ x y
  --   → Z₀Prop.ιᶻ x Z₀.≤≥ Z₀Prop.ιᶻ y 
  --   → ιᶻ x ≤ ιᶻ y ∧ ιᶻ y ≤ ιᶻ x
  -- ιᶻ≤≥ιᶻ x y (∧i p , q) = ∧i ιᶻ≤ιᶻ x y p , ιᶻ≤ιᶻ y x q

record ExtensionalPlumpOrdinals : Setω where
  field
    Zᴬe : ∀ {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
        → ExtensionalPlumpAlgebra S P
  
