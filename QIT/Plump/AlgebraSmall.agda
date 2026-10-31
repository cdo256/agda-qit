open import QIT.Prelude hiding (⊥ˢ)
open import QIT.Prop hiding (⊥; _∨_)
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.AlgebraSmall
  ⦃ pathElim* : PathElim ⦄       
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  where

data Sᶻ : Set ℓS where
  ιˢ : S → Sᶻ
  ⊥ˢ : Sᶻ
  ∨ˢ : Sᶻ

data Pᶻ : Sᶻ → Set (ℓS ⊔ ℓP) where
  ιᵖ : ∀ s → P s → Pᶻ (ιˢ s)
  ∨-lᵖ : Pᶻ ∨ˢ
  ∨-rᵖ : Pᶻ ∨ˢ

record PlumpAlgebra
  : Set (lsuc ℓS ⊔ lsuc ℓP) where

  infix 4 _≤_ _<_

  field
    Z : Set (ℓS ⊔ ℓP)
    sup : Σ Sᶻ (λ s → Pᶻ s → Z) → Z
    _<_ : Z → Z → Prop (ℓS ⊔ ℓP)
    _≤_ : Z → Z → Prop (ℓS ⊔ ℓP)

    sup≤ : {s : Sᶻ} {f : Pᶻ s → Z} {α : Z}
          → (∀ i → f i < α)
          → sup (s , f) ≤ α
    <sup : {s : Sᶻ} {f : Pᶻ s → Z}
          → (i : Pᶻ s) → {α : Z}
          → α ≤ f i
          → α < sup (s , f)

record ExtensionalPlumpAlgebra
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    Zᴬ : PlumpAlgebra

  open PlumpAlgebra Zᴬ public

  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β

record Displayed
  (A : PlumpAlgebra)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module A = PlumpAlgebra A
  field
    Zᴰ : A.Z → Set (ℓS ⊔ ℓP)
    supᴰ : ∀ s {f : Pᶻ s → A.Z}
         → (∀ i → Zᴰ (f i))
         → Zᴰ (A.sup (s , f))
    _⊢_<ᴰ_ : ∀ {α β} → α A.< β → Zᴰ α → Zᴰ β → Prop (ℓS ⊔ ℓP)
    _⊢_≤ᴰ_ : ∀ {α β} → α A.≤ β → Zᴰ α → Zᴰ β → Prop (ℓS ⊔ ℓP)

    sup≤ᴰ : ∀ {s : Sᶻ} {f : Pᶻ s → A.Z} {α : A.Z}
              {fᴰ : ∀ i → Zᴰ (f i)} {αᴰ : Zᴰ α}
          → (p : ∀ i → f i A.< α)
          → (∀ i → p i ⊢ fᴰ i <ᴰ αᴰ)
          → A.sup≤ p ⊢ supᴰ s fᴰ ≤ᴰ αᴰ
    <supᴰ : ∀ {s : Sᶻ} {f : Pᶻ s → A.Z} {α : A.Z}
              {fᴰ : ∀ i → Zᴰ (f i)} {αᴰ : Zᴰ α}
          → (i : Pᶻ s)
          → (p : α A.≤ f i)
          → p ⊢ αᴰ ≤ᴰ fᴰ i
          → A.<sup i p ⊢ αᴰ <ᴰ supᴰ s fᴰ

record Elim
  {A : PlumpAlgebra}
  (D : Displayed A)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  private
    module A = PlumpAlgebra A
  module D = Displayed D
  field
    Zᴱ : ∀ α → D.Zᴰ α
    supᴱ : ∀ s (f : Pᶻ s → A.Z)
         → D.supᴰ s (λ i → Zᴱ (f i)) ≡ Zᴱ (A.sup (s , f))
    <ᴱ : ∀ {α β} (p : α A.< β)
       → p D.⊢ Zᴱ α <ᴰ Zᴱ β
    ≤ᴱ : ∀ {α β} (p : α A.≤ β)
       → p D.⊢ Zᴱ α ≤ᴰ Zᴱ β

  open Displayed D public

record _≈ᴱ_
  {A : PlumpAlgebra} {D : Displayed A}
  (e₁ e₂ : Elim D)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  constructor mk≈
  module e₁ = Elim e₁
  module e₂ = Elim e₂
  field
    Zᴱ : ∀ α → e₁.Zᴱ α ≡ e₂.Zᴱ α

record IsExtensionalᴰ
  (Ae : ExtensionalPlumpAlgebra)
  (D : Displayed (ExtensionalPlumpAlgebra.Zᴬ Ae))
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  constructor mkext
  module A = ExtensionalPlumpAlgebra Ae
  module D = Displayed D
  field
    antisymᴰ : ∀ {α β} (p : α A.≤ β) (q : β A.≤ α)
             → {αᴰ : D.Zᴰ α} {βᴰ : D.Zᴰ β}
             → p D.⊢ αᴰ ≤ᴰ βᴰ
             → q D.⊢ βᴰ ≤ᴰ αᴰ
             → subst D.Zᴰ (A.antisym p q) αᴰ ≡ βᴰ

-- RelationDisplayed
--   : (A : PlumpAlgebra)
--   → (C< : ∀ {α β} → PlumpAlgebra._<_ A α β → Prop (ℓS ⊔ ℓP))
--   → (C≤ : ∀ {α β} → PlumpAlgebra._≤_ A α β → Prop (ℓS ⊔ ℓP))
--   → (∀ {s : Sᶻ} {f : Pᶻ s → PlumpAlgebra.Z A} {α}
--        (p : ∀ i → PlumpAlgebra._<_ A (f i) α)
--      → (∀ i → C< (p i))
--      → C≤ (PlumpAlgebra.sup≤ A p))
--   → (∀ {s : Sᶻ} {f : Pᶻ s → PlumpAlgebra.Z A} {α}
--        (i : Pᶻ s) (p : PlumpAlgebra._≤_ A α (f i))
--      → C≤ p
--      → C< (PlumpAlgebra.<sup A i p))
--   → Displayed A
-- RelationDisplayed A C< C≤ sup≤ᴰ' <supᴰ' = record
--   { Zᴰ = λ _ → ⊤ˢ*
--   ; supᴰ = λ _ _ → tt*
--   ; _⊢_<ᴰ_ = λ p _ _ → C< p
--   ; _⊢_≤ᴰ_ = λ p _ _ → C≤ p
--   ; sup≤ᴰ = sup≤ᴰ'
--   ; <supᴰ = <supᴰ'
--   }

record DisplayedProp
  (A : PlumpAlgebra)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module A = PlumpAlgebra A
  field
    Zᴰ : A.Z → Prop (ℓS ⊔ ℓP)
    supᴰ : ∀ s {f : Pᶻ s → A.Z}
         → (∀ i → Zᴰ (f i))
         → Zᴰ (A.sup (s , f))

  D : Displayed A
  D = record
    { Zᴰ = λ x → Box (Zᴰ x)
    ; supᴰ = λ s p → box (supᴰ s (λ i → p i .unbox))
    ; _⊢_<ᴰ_ = λ _ _ _ → ⊤*
    ; _⊢_≤ᴰ_ = λ _ _ _ → ⊤*
    ; sup≤ᴰ = λ _ _ → tt*
    ; <supᴰ = λ _ _ _ → tt*
    }


{-
RelationDisplayed-extensional
  : (Ae : ExtensionalPlumpAlgebra)
  → (C< : ∀ {α β} → ExtensionalPlumpAlgebra._<_ Ae α β → Prop (ℓS ⊔ ℓP))
  → (C≤ : ∀ {α β} → ExtensionalPlumpAlgebra._≤_ Ae α β → Prop (ℓS ⊔ ℓP))
  → (sup≤ᴰ' : ∀ {s : Sᶻ} {f : Pᶻ s → ExtensionalPlumpAlgebra.Z Ae} {α}
       (p : ∀ i → ExtensionalPlumpAlgebra._<_ Ae (f i) α)
     → (∀ i → C< (p i))
     → C≤ (ExtensionalPlumpAlgebra.sup≤ Ae p))
  → (<supᴰ' : ∀ {s : Sᶻ} {f : Pᶻ s → ExtensionalPlumpAlgebra.Z Ae} {α}
       (i : Pᶻ s) (p : ExtensionalPlumpAlgebra._≤_ Ae α (f i))
     → C≤ p
     → C< (ExtensionalPlumpAlgebra.<sup Ae i p))
  → IsExtensionalᴰ Ae
      (RelationDisplayed (ExtensionalPlumpAlgebra.Zᴬ Ae)
        C< C≤ sup≤ᴰ' <supᴰ')
RelationDisplayed-extensional Ae C< C≤ sup≤ᴰ' <supᴰ' = record
  { antisymᴰ = λ p q {αᴰ} {βᴰ} _ _
      → const-⊤-subst (ExtensionalPlumpAlgebra.antisym Ae p q) αᴰ βᴰ }
  where
  const-⊤-subst
    : ∀ {α β : ExtensionalPlumpAlgebra.Z Ae}
    → (p : α ≡ β) (x y : ⊤ˢ*)
    → subst (λ _ → ⊤ˢ*) p x ≡ y
  const-⊤-subst p (lift tt) (lift tt) = ≡.subst-const ⊤ˢ* tt* p
-}

record PlumpHom
  (A B : PlumpAlgebra)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module A = PlumpAlgebra A
  module B = PlumpAlgebra B
  field
    Z : A.Z → B.Z
    sup : (s : Sᶻ)
      → (f : Pᶻ s → A.Z)
      → Z (A.sup (s , f)) ≡ B.sup (s , λ i → Z (f i))
    _<_ : ∀ {α β} → α A.< β → Z α B.< Z β
    _≤_ : ∀ {α β} → α A.≤ β → Z α B.≤ Z β

record _≈ᵖ_
  {A B : PlumpAlgebra}
  (f g : PlumpHom A B)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module f = PlumpHom f
  module g = PlumpHom g
  field
    Z : ∀ α → f.Z α ≡ g.Z α

ConstDisplayed : (A B : PlumpAlgebra) → Displayed A
ConstDisplayed A B = record
  { Zᴰ = λ _ → B.Z
  ; supᴰ = λ s f → B.sup (s , f)
  ; _⊢_<ᴰ_ = λ _ x y → x B.< y
  ; _⊢_≤ᴰ_ = λ _ x y → x B.≤ y
  ; sup≤ᴰ = λ _ p → B.sup≤ p
  ; <supᴰ = λ i _ p → B.<sup i p
  }
  where
  module B = PlumpAlgebra B

ConstDisplayed-extensional
  : (Ae Be : ExtensionalPlumpAlgebra)
  → IsExtensionalᴰ Ae
      (ConstDisplayed (ExtensionalPlumpAlgebra.Zᴬ Ae)
                      (ExtensionalPlumpAlgebra.Zᴬ Be))
ConstDisplayed-extensional Ae Be = record
  { antisymᴰ = λ p q {x} {y} xy yx →
      ≡.trans
        (≡.subst-const B.Z x (A.antisym p q))
        (B.antisym xy yx)
  }
  where
  module A = ExtensionalPlumpAlgebra Ae
  module B = ExtensionalPlumpAlgebra Be

elim→hom
  : ∀ {A B : PlumpAlgebra}
  → Elim (ConstDisplayed A B)
  → PlumpHom A B
elim→hom e = record
  { Z = E.Zᴱ
  ; sup = λ s f → ≡.sym (E.supᴱ s f)
  ; _<_ = E.<ᴱ
  ; _≤_ = E.≤ᴱ
  }
  where
  module E = Elim e

hom→elim
  : ∀ {A B : PlumpAlgebra}
  → PlumpHom A B
  → Elim (ConstDisplayed A B)
hom→elim h = record
  { Zᴱ = H.Z
  ; supᴱ = λ s f → ≡.sym (H.sup s f)
  ; <ᴱ = H._<_
  ; ≤ᴱ = H._≤_
  }
  where
  module H = PlumpHom h

record InitialExtensionalPlumpOrdinals
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  open ExtensionalPlumpAlgebra
  field
    Zᴬe : ExtensionalPlumpAlgebra

  module I = ExtensionalPlumpAlgebra Zᴬe
  field
    elimZᴬ
      : (D : Displayed I.Zᴬ)
      → IsExtensionalᴰ Zᴬe D
      → Elim D
    elim!Zᴬ
      : (D : Displayed I.Zᴬ)
      → (De : IsExtensionalᴰ Zᴬe D)
      → (e : Elim D)
      → e ≈ᴱ elimZᴬ D De

  recZᴬ
    : (Zᴬ' : ExtensionalPlumpAlgebra)
    → PlumpHom I.Zᴬ (Zᴬ' .Zᴬ)
  recZᴬ Zᴬ' = elim→hom
    (elimZᴬ (ConstDisplayed I.Zᴬ (Zᴬ' .Zᴬ))
      (ConstDisplayed-extensional Zᴬe Zᴬ'))

  rec!Zᴬ
    : (Zᴬ' : ExtensionalPlumpAlgebra)
    → (f : PlumpHom I.Zᴬ (Zᴬ' .Zᴬ))
    → f ≈ᵖ recZᴬ Zᴬ'
  rec!Zᴬ Zᴬ' f = record
    { Z = _≈ᴱ_.Zᴱ
        (elim!Zᴬ
          (ConstDisplayed I.Zᴬ (Zᴬ' .Zᴬ))
          (ConstDisplayed-extensional Zᴬe Zᴬ')
          (hom→elim f))
    }
  elimp : 
    (Zᴰ : I.Z → Prop (ℓS ⊔ ℓP))
    (supᴰ : ∀ s {f : Pᶻ s → I.Z}
          → (∀ i → Zᴰ (f i))
          → Zᴰ (I.sup (s , f)))
    → ∀ α → Zᴰ α
  elimp Zᴰ supᴰ α = {!e.Zᴱ!}
    where
    D : DisplayedProp I.Zᴬ
    D = record
      { Zᴰ = Zᴰ
      ; supᴰ = supᴰ }
    module D = DisplayedProp D
    e : Elim D.D
    e = elimZᴬ D.D (mkext λ _ _ _ _ → ≡.refl)
    module e = Elim e

  open ExtensionalPlumpAlgebra Zᴬe public

