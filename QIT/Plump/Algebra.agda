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

record Displayed
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  (Zᴬ : PlumpAlgebra S P)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  open PlumpAlgebra Zᴬ
  field
    Zᴰ : Z → Set (ℓS ⊔ ℓP)
    supᴰ : ∀ s → {ξ : P s → Z} (f : ∀ i → Zᴰ (ξ i)) → Zᴰ (sup (s , ξ))
    _⊢_<ᴰ_ : ∀ {α β} → α < β → Zᴰ α → Zᴰ β → Prop (ℓS ⊔ ℓP)
    _⊢_≤ᴰ_ : ∀ {α β} → α ≤ β → Zᴰ α → Zᴰ β → Prop (ℓS ⊔ ℓP)

    sup≤ᴰ : {s : S} {ξ : P s → Z} {α : Z}
          → {f : ∀ i → Zᴰ (ξ i)}
          → {x : Zᴰ α}
          → (p : ∀ i → ξ i < α)
          → (∀ i → p i ⊢ f i <ᴰ x)
          → sup≤ p ⊢ supᴰ s f ≤ᴰ x
    <supᴰ : {s : S} {ξ : P s → Z} {α : Z}
          → {f : ∀ i → Zᴰ (ξ i)} {x : Zᴰ α}
          → (i : P s)
          → (p : α ≤ ξ i)
          → p ⊢ x ≤ᴰ f i
          → <sup i p ⊢ x <ᴰ supᴰ s f

    ≤≤ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β ≤ γ} → {p : α ≤ β}
        → q ⊢ y ≤ᴰ z → p ⊢ x ≤ᴰ y → ≤≤ q p ⊢ x ≤ᴰ z
    <≤ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β < γ} → {p : α ≤ β}
        → q ⊢ y <ᴰ z → p ⊢ x ≤ᴰ y → <≤ q p ⊢ x <ᴰ z
    ≤<ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β ≤ γ} → {p : α < β}
        → q ⊢ y ≤ᴰ z → p ⊢ x <ᴰ y → ≤< q p ⊢ x <ᴰ z
    <<ᴰ : {α β γ : Z} {x : Zᴰ α} {y : Zᴰ β} {z : Zᴰ γ}
        → {q : β < γ} → {p : α < β}
        → q ⊢ y <ᴰ z → p ⊢ x <ᴰ y → << q p ⊢ x <ᴰ z
    <→≤ᴰ : {α β : Z} {p : α < β} {x : Zᴰ α} {y : Zᴰ β}
         → p ⊢ x <ᴰ y → <→≤ p ⊢ x ≤ᴰ y

    ≤reflᴰ : ∀ {α} {x : Zᴰ α} → ≤refl α ⊢ x ≤ᴰ x

record Elim
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {Zᴬ : PlumpAlgebra S P}
  (ZD : Displayed Zᴬ)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  open PlumpAlgebra Zᴬ
  open Displayed ZD
  field
    Zᴱ : ∀ α → Zᴰ α
    supᴱ : ∀ s (ξ : P s → Z)
         → supᴰ s (λ i → Zᴱ (ξ i)) ≡ Zᴱ (sup (s , ξ))
    <ᴱ : ∀ {α β} → (p : α < β) → p ⊢ Zᴱ α <ᴰ Zᴱ β
    ≤ᴱ : ∀ {α β} → (p : α ≤ β) → p ⊢ Zᴱ α ≤ᴰ Zᴱ β

record Hom
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  (Zᴬ Zᴮ : PlumpAlgebra S P)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module Zᴬ = PlumpAlgebra Zᴬ
  module Zᴮ = PlumpAlgebra Zᴮ
  field
    Zʰ : Zᴬ.Z → Zᴮ.Z
    supʰ : ∀ s (ξ : P s → Zᴬ.Z)
         → Zʰ (Zᴬ.sup (s , ξ)) ≡ Zᴮ.sup (s , λ i → Zʰ (ξ i))
    <ʰ : ∀ {α β} → Zᴬ._<_ α β → Zᴮ._<_ (Zʰ α) (Zʰ β)
    ≤ʰ : ∀ {α β} → Zᴬ._≤_ α β → Zᴮ._≤_ (Zʰ α) (Zʰ β)

record _≈ʰ_
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {Zᴬ Zᴮ : PlumpAlgebra S P}
  (f g : Hom Zᴬ Zᴮ)
  : Prop (ℓS ⊔ ℓP) where
  module f = Hom f
  module g = Hom g
  field
    ≈Zʰ : ∀ α → f.Zʰ α ≡ g.Zʰ α

record _≈ᴱ_
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {Zᴬ : PlumpAlgebra S P} {ZD : Displayed Zᴬ}
  (e₁ e₂ : Elim ZD)
  : Prop (lsuc ℓS ⊔ lsuc ℓP) where
  module e₁ = Elim e₁
  module e₂ = Elim e₂
  field
    Zᴱ : ∀ α → e₁.Zᴱ α ≡ e₂.Zᴱ α

module _
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {Zᴬ Zᴮ : PlumpAlgebra S P}
  where
  module Zᴬ = PlumpAlgebra Zᴬ
  module Zᴮ = PlumpAlgebra Zᴮ

  Constᴰ : Displayed Zᴬ
  Constᴰ = record
    { Zᴰ = λ _ → Zᴮ.Z
    ; supᴰ = λ s f → Zᴮ.sup (s , f)
    ; _⊢_<ᴰ_ = λ _ x y → Zᴮ._<_ x y
    ; _⊢_≤ᴰ_ = λ _ x y → Zᴮ._≤_ x y
    ; sup≤ᴰ = λ _ r → Zᴮ.sup≤ r
    ; <supᴰ = λ i _ r → Zᴮ.<sup i r
    ; ≤≤ᴰ = λ yz xy → Zᴮ.≤≤ yz xy
    ; <≤ᴰ = λ yz xy → Zᴮ.<≤ yz xy
    ; ≤<ᴰ = λ yz xy → Zᴮ.≤< yz xy
    ; <<ᴰ = λ yz xy → Zᴮ.<< yz xy
    ; <→≤ᴰ = λ xy → Zᴮ.<→≤ xy
    ; ≤reflᴰ = Zᴮ.≤refl _
    }

  hom→elim : Hom Zᴬ Zᴮ → Elim Constᴰ
  hom→elim h = record
    { Zᴱ = H.Zʰ
    ; supᴱ = λ s ξ → ≡.sym (H.supʰ s ξ)
    ; <ᴱ = H.<ʰ
    ; ≤ᴱ = H.≤ʰ
    }
    where
    module H = Hom h

  elim→hom : Elim Constᴰ → Hom Zᴬ Zᴮ
  elim→hom e = record
    { Zʰ = E.Zᴱ
    ; supʰ = λ s ξ → ≡.sym (E.supᴱ s ξ)
    ; <ʰ = E.<ᴱ
    ; ≤ʰ = E.≤ᴱ
    }
    where
    module E = Elim e

  elim≈→hom≈ : ∀ {e₁ e₂ : Elim Constᴰ}
             → e₁ ≈ᴱ e₂ → elim→hom e₁ ≈ʰ elim→hom e₂
  elim≈→hom≈ p = record { ≈Zʰ = _≈ᴱ_.Zᴱ p }

record IsExtensional
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  (Zᴬ : PlumpAlgebra S P)
  : Prop (ℓS ⊔ ℓP) where
  open PlumpAlgebra Zᴬ
  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

record IsExtensionalᴰ
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {Zᴬ : PlumpAlgebra S P}
  (ZD : Displayed Zᴬ)
  : Prop (ℓS ⊔ ℓP) where
  open PlumpAlgebra Zᴬ
  open Displayed ZD
  field
    isExtZᴬ : IsExtensional Zᴬ

  open IsExtensional isExtZᴬ public
  field
    antisymᴰ : ∀ {α β} → (p : α ≤ β) → (q : β ≤ α)
             → {x : Zᴰ α} {y : Zᴰ β}
             → p ⊢ x ≤ᴰ y → q ⊢ y ≤ᴰ x
             → subst Zᴰ (antisym p q) x ≡ y

module _
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {Zᴬ Zᴮ : PlumpAlgebra S P}
  where
  module A = PlumpAlgebra Zᴬ
  module B = PlumpAlgebra Zᴮ

  const-subst : ∀ {α β : A.Z} (r : α ≡ β) (x : B.Z)
              → subst (Displayed.Zᴰ (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})) r x ≡ x
  const-subst {α} r x = ≡.Jp Q r u
    where
    Q : ∀ β (r : α ≡ β) → Prop _
    Q β r = subst (Displayed.Zᴰ (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})) r x ≡ x

    u : subst (Displayed.Zᴰ (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})) ≡.refl x ≡ x
    u = ≡.subst-refl x

  const-isExtensionalᴰ
    : IsExtensional Zᴬ → IsExtensional Zᴮ
    → IsExtensionalᴰ (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})
  const-isExtensionalᴰ extZᴬ extZᴮ = record
    { isExtZᴬ = extZᴬ
    ; antisymᴰ = λ p q {x} {y} xy yx →
      ≡.trans
        (const-subst (IsExtensional.antisym extZᴬ p q) x)
        (IsExtensional.antisym extZᴮ xy yx)
    }

record IsInitial
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  (Zᴬ : PlumpAlgebra S P)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    elim : (ZD : Displayed Zᴬ) → Elim ZD
    elim-unique : ∀ ZD → (e : Elim ZD) → elim ZD ≈ᴱ e

  recʰ : (Zᴮ : PlumpAlgebra S P) → Hom Zᴬ Zᴮ
  recʰ Zᴮ = elim→hom {Zᴬ = Zᴬ} {Zᴮ = Zᴮ}
    (elim (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ}))

  recʰ-unique : ∀ Zᴮ → (fʰ : Hom Zᴬ Zᴮ) → recʰ Zᴮ ≈ʰ fʰ
  recʰ-unique Zᴮ fʰ =
    elim≈→hom≈ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ}
      (elim-unique
        (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})
        (hom→elim {Zᴬ = Zᴬ} {Zᴮ = Zᴮ} fʰ))

record IsInitialExt
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  (Zᴬ : PlumpAlgebra S P)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    ext : IsExtensional Zᴬ
    elim : (ZD : Displayed Zᴬ) → IsExtensionalᴰ ZD → Elim ZD
    elim-unique : ∀ ZD isExtZD e → elim ZD isExtZD ≈ᴱ e

  recʰ : ∀ {Zᴮ : PlumpAlgebra S P} → IsExtensional Zᴮ → Hom Zᴬ Zᴮ
  recʰ {Zᴮ} extZᴮ =
    elim→hom {Zᴬ = Zᴬ} {Zᴮ = Zᴮ}
      (elim
        (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})
        (const-isExtensionalᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ} ext extZᴮ))

  recʰ-unique
    : ∀ {Zᴮ : PlumpAlgebra S P} (extZᴮ : IsExtensional Zᴮ)
    → (fʰ : Hom Zᴬ Zᴮ) → recʰ extZᴮ ≈ʰ fʰ
  recʰ-unique {Zᴮ} extZᴮ fʰ =
    elim≈→hom≈ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ}
      (elim-unique
        (Constᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ})
        (const-isExtensionalᴰ {Zᴬ = Zᴬ} {Zᴮ = Zᴮ} ext extZᴮ)
        (hom→elim {Zᴬ = Zᴬ} {Zᴮ = Zᴮ} fʰ))

record ExtensionalPlumpAlgebra
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    Zᴬ : PlumpAlgebra S P

  open PlumpAlgebra Zᴬ public

  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

  isExtensional : IsExtensional Zᴬ
  isExtensional = record { antisym = antisym }

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
  
