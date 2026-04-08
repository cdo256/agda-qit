open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
open import QIT.Setoid.Base renaming (_[_≈_] to _⟦_≈_⟧)
open import QIT.Relation.Binary using (IsEquivalence)
import QIT.Relation.SetQuotient as Q

module QIT.Setoid.Quotient where

_/≈ : ∀ {ℓA ℓR} (Ã : Setoid ℓA ℓR) → Set (ℓA ⊔ ℓR)
Ã /≈ = A Q./ _≈_
  where
  open Setoid Ã renaming (Carrier to A)

module SetoidQuotient {ℓA ℓR} (Ã : Setoid ℓA ℓR) where
  open Setoid Ã renaming (Carrier to A)
  [_] : A → Ã /≈
  [_] = Q.[_]

  ≈[_] : ∀ {x y} → x ≈ y → [ x ] ≡ [ y ]
  ≈[_] p = Q.quot-rel _ _ p

  rec
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : {x y : A} → x ≈ y → f x ≡ f y)
    → Ã /≈ → B
  rec f eq = Q.quot-rec f λ _ _ → eq

  rec₂
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → A → B)
    → (eq : {x y z w : A} → x ≈ y → z ≈ w → f x z ≡ f y w)
    → Ã /≈ → Ã /≈ → B
  rec₂ {B = B} f eq = rec g g-cong
    where
    g : A → Ã /≈ → B
    g x = rec (f x) (eq refl)
    g-cong : ∀ {x y} → x ≈ y → g x ≡ g y
    g-cong {x} {y} p =
      ≡.funExt (Q.quot-elimp
        (λ z → rec (f x) (eq refl) z ≡ rec (f y) (eq refl) z)
        (λ a → eq p refl))

  elim
    : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : {x y : A} → (r : x ≈ y) → subst B ≈[ r ] (f x) ≡ (f y))
    → ∀ a/ → B a/
  elim B f eq = Q.quot-elim B f λ _ _ → eq

  recp : ∀ {ℓB} {B : Prop ℓB}
    → (f : A → B)
    → Ã /≈ → B
  recp f x = Q.quot-recp f x

  elimp : ∀ {ℓB} (B : Ã /≈ → Prop ℓB)
    → (f : ∀ a → B [ a ])
    → ∀ a/ → B a/
  elimp B f a/ = Q.quot-elimp B f a/


  effectiveness : ∀ x y → [ x ] ≡ [ y ] → x ≈ y
  effectiveness x y p = unbox (≡.subst P p (box refl))
    where
    P : Ã /≈ → Set ℓR
    P = rec
          (λ a → Box (x ≈ a))
          (λ a≈b → ≡.cong Box (propExt (x≈a⇔x≈b a≈b)))
      where
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b = (λ x≈a → trans x≈a a≈b)
                  , (λ x≈b → trans x≈b (sym a≈b))

  cong
    : ∀ {ℓB} {B : Set ℓB}
    → (f : Ã /≈ → B)
    → A → B
  cong f x = f [ x ]

  rec-beta
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : {x y : A} → x ≈ y → f x ≡ f y) (x : A)
    → rec f eq [ x ] ≡ f x
  rec-beta f eq x = Q.quot-rec-beta f (λ _ _ → eq) x

  elim-beta
    : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : {x y : A} → (r : x ≈ y) → subst B ≈[ r ] (f x) ≡ (f y))
    → (x : A)
    → elim B f eq [ x ] ≡ f x
  elim-beta B f eq x = Q.quot-elim-beta B f (λ _ _ → eq) x

  map : ∀ {ℓB ℓS} (B̃ : Setoid ℓB ℓS) (f₀ : ⟨ Ã ⟩ → ⟨ B̃ ⟩) (f-cong : ∀ {x y : ⟨ Ã ⟩} → x ≈ y → B̃ ⟦ f₀ x ≈ f₀ y ⟧) → Ã /≈ → B̃ /≈
  map B̃ f₀ f-cong = rec (λ x → Q.[ f₀ x ]) λ {x} {y} p → Q.quot-rel (f₀ x) (f₀ y) (f-cong p)
    where
    module B = Setoid B̃
