open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.Algebra
  ⦃ pathElim* : PathElim ⦄       
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

record Algebra ℓA : Set (lsuc ℓA ⊔ lsuc ℓS ⊔ lsuc ℓP) where
  field
    Z : Set ℓA
    sup : Σ S (λ s → P s → Z) → Z
    _<_ : Z → Z → Prop ℓA
    _≤_ : Z → Z → Prop ℓA

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

    iswf< : WellFounded _<_

record Displayed ℓA (Zᴬ : Algebra ℓA) 
  : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra Zᴬ
  field
    Zᴰ : Z → Set ℓA
    supᴰ : ∀ s → {ξ : P s → Z} (f : ∀ i → Zᴰ (ξ i)) → Zᴰ (sup (s , ξ))
    _⊢_<ᴰ_ : ∀ {α β} → α < β → Zᴰ α → Zᴰ β → Prop ℓA
    _⊢_≤ᴰ_ : ∀ {α β} → α ≤ β → Zᴰ α → Zᴰ β → Prop ℓA

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

    --TODO: Do I need this in the displayed models?
    -- iswf< : WellFounded _<ᴰ_

record Elim {ℓA} {ZA : Algebra ℓA}
  (ZD : Displayed ℓA ZA)
  : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra ZA
  open Displayed ZD
  field
    Zᴱ : ∀ α → Zᴰ α
    supᴱ : ∀ s (ξ : P s → Z)
         → supᴰ s (λ i → Zᴱ (ξ i)) ≡ Zᴱ (sup (s , ξ))
    <ᴱ : ∀ {α β} → (p : α < β) → p ⊢ Zᴱ α <ᴰ Zᴱ β
    ≤ᴱ : ∀ {α β} → (p : α ≤ β) → p ⊢ Zᴱ α ≤ᴰ Zᴱ β

record Hom {ℓA} (ZA ZB : Algebra ℓA)
  : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  module ZA = Algebra ZA
  module ZB = Algebra ZB
  field
    Zʰ : ZA.Z → ZB.Z
    supʰ : ∀ s (ξ : P s → ZA.Z)
        → Zʰ (ZA.sup (s , ξ)) ≡ ZB.sup (s , λ i → Zʰ (ξ i))
    <ʰ : ∀ {α β} → ZA._<_ α β → ZB._<_ (Zʰ α) (Zʰ β)
    ≤ʰ : ∀ {α β} → ZA._≤_ α β → ZB._≤_ (Zʰ α) (Zʰ β)

record _≈ʰ_ {ℓA} {ZA ZB : Algebra ℓA}
             (f g : Hom ZA ZB)
             : Prop (ℓS ⊔ ℓP ⊔ ℓA) where
  module f = Hom f
  module g = Hom g
  field
    ≈Zʰ : ∀ α → f.Zʰ α ≡ g.Zʰ α

record _≈ᴱ_ {ℓA} {ZA : Algebra ℓA} {ZD : Displayed ℓA ZA}
              (e₁ e₂ : Elim ZD) : Prop (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  module e₁ = Elim e₁
  module e₂ = Elim e₂
  field
    Zᴱ : ∀ α → e₁.Zᴱ α ≡ e₂.Zᴱ α

module _ {ℓA} {ZA ZB : Algebra ℓA} where
  module ZA = Algebra ZA
  module ZB = Algebra ZB

  Constᴰ : Displayed ℓA ZA
  Constᴰ = record
    { Zᴰ = λ _ → ZB.Z
    ; supᴰ = λ s f → ZB.sup (s , f)
    ; _⊢_<ᴰ_ = λ _ x y → ZB._<_ x y
    ; _⊢_≤ᴰ_ = λ _ x y → ZB._≤_ x y
    ; sup≤ᴰ = λ _ r → ZB.sup≤ r
    ; <supᴰ = λ i _ r → ZB.<sup i r
    ; ≤≤ᴰ = λ yz xy → ZB.≤≤ yz xy
    ; <≤ᴰ = λ yz xy → ZB.<≤ yz xy
    ; ≤<ᴰ = λ yz xy → ZB.≤< yz xy
    ; <<ᴰ = λ yz xy → ZB.<< yz xy
    ; <→≤ᴰ = λ xy → ZB.<→≤ xy
    ; ≤reflᴰ = ZB.≤refl _
    }

  hom→elim : Hom ZA ZB → Elim Constᴰ
  hom→elim h = record
    { Zᴱ = H.Zʰ
    ; supᴱ = λ s ξ → ≡.sym (H.supʰ s ξ)
    ; <ᴱ = H.<ʰ
    ; ≤ᴱ = H.≤ʰ
    }
    where
    module H = Hom h

  elim→hom : Elim Constᴰ → Hom ZA ZB
  elim→hom e = record
    { Zʰ = E.Zᴱ
    ; supʰ = λ s ξ → ≡.sym (E.supᴱ s ξ)
    ; <ʰ = E.<ᴱ
    ; ≤ʰ = E.≤ᴱ
    }
    where
    module E = Elim e

  elim≈→hom≈ : ∀ {e₁ e₂ : Elim Constᴰ} → e₁ ≈ᴱ e₂ → elim→hom e₁ ≈ʰ elim→hom e₂
  elim≈→hom≈ p = record { ≈Zʰ = _≈ᴱ_.Zᴱ p }

record IsExtensional {ℓA} (ZA : Algebra ℓA) : Prop ℓA where
  open Algebra ZA
  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

record IsExtensionalᴰ {ℓA} {ZA : Algebra ℓA} (ZD : Displayed ℓA ZA) : Prop ℓA where
  open Algebra ZA
  open Displayed ZD
  field
    isExtZA : IsExtensional ZA

  open IsExtensional isExtZA public
  field
    antisymᴰ : ∀ {α β} → (p : α ≤ β) → (q : β ≤ α)
            → {x : Zᴰ α} {y : Zᴰ β}
            → p ⊢ x ≤ᴰ y → q ⊢ y ≤ᴰ x
            → subst Zᴰ (antisym p q) x ≡ y

module _ {ℓA} {ZA ZB : Algebra ℓA} where
  const-subst : ∀ {α β : ZA .Algebra.Z} (r : α ≡ β) (x : ZB .Algebra.Z)
              → subst (Displayed.Zᴰ (Constᴰ {ZA = ZA} {ZB = ZB})) r x ≡ x
  const-subst {α} r x = ≡.Jp Q r u
    where
    Q : ∀ β (r : α ≡ β) → Prop _
    Q β r = subst (Displayed.Zᴰ (Constᴰ {ZA = ZA} {ZB = ZB})) r x ≡ x

    u : subst (Displayed.Zᴰ (Constᴰ {ZA = ZA} {ZB = ZB})) ≡.refl x ≡ x
    u = ≡.subst-refl x

  const-isExtensionalᴰ : IsExtensional ZA → IsExtensional ZB → IsExtensionalᴰ (Constᴰ {ZA = ZA} {ZB = ZB})
  const-isExtensionalᴰ extZA extZB = record
    { isExtZA = extZA
    ; antisymᴰ = λ p q {x} {y} xy yx →
      ≡.trans
        (const-subst (IsExtensional.antisym extZA p q) x)
        (IsExtensional.antisym extZB xy yx)
    }

record IsInitial {ℓA} (ZA : Algebra ℓA) : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra ZA
  field
    elim : (ZD : Displayed ℓA ZA) → Elim ZD
    elim-unique : ∀ ZD → (e : Elim ZD) → elim ZD ≈ᴱ e

  recʰ : (ZB : Algebra ℓA) → Hom ZA ZB
  recʰ ZB = elim→hom {ZA = ZA} {ZB = ZB} (elim (Constᴰ {ZA = ZA} {ZB = ZB}))

  recʰ-unique : ∀ ZB → (fʰ : Hom ZA ZB) → recʰ ZB ≈ʰ fʰ
  recʰ-unique ZB fʰ =
    elim≈→hom≈ {ZA = ZA} {ZB = ZB}
      (elim-unique (Constᴰ {ZA = ZA} {ZB = ZB}) (hom→elim {ZA = ZA} {ZB = ZB} fʰ))

record IsInitialExt {ℓA} (ZA : Algebra ℓA) : Set (ℓS ⊔ ℓP ⊔ lsuc ℓA) where
  open Algebra ZA
  field
    ext : IsExtensional ZA
    elim : (ZD : Displayed ℓA ZA)
         → IsExtensionalᴰ ZD
         → Elim ZD
    elim-unique : ∀ ZD isExtZD e → elim ZD isExtZD ≈ᴱ e

  recʰ : ∀ {ZB : Algebra ℓA} → IsExtensional ZB → Hom ZA ZB
  recʰ {ZB} extZB =
    elim→hom {ZA = ZA} {ZB = ZB}
      (elim (Constᴰ {ZA = ZA} {ZB = ZB}) (const-isExtensionalᴰ {ZA = ZA} {ZB = ZB} ext extZB))

  recʰ-unique : ∀ {ZB : Algebra ℓA} (extZB : IsExtensional ZB) → (fʰ : Hom ZA ZB) → recʰ extZB ≈ʰ fʰ
  recʰ-unique {ZB} extZB fʰ =
    elim≈→hom≈ {ZA = ZA} {ZB = ZB}
      (elim-unique (Constᴰ {ZA = ZA} {ZB = ZB})
                   (const-isExtensionalᴰ {ZA = ZA} {ZB = ZB} ext extZB)
                   (hom→elim {ZA = ZA} {ZB = ZB} fʰ))
