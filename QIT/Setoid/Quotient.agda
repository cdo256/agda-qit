open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
open import QIT.Setoid.Base
open import QIT.Relation.Binary using (IsEquivalence)
import QIT.Relation.SetQuotient as Q

module QIT.Setoid.Quotient where

module _ {ℓA ℓR} (Ã : Setoid ℓA ℓR) where
  open Setoid Ã renaming (Carrier to A)
  _/≈ : Set (ℓA ⊔ ℓR)
  _/≈ = A Q./ _≈_

  [_] : A → _/≈
  [_] = Q.[_]

  quot-rec
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → x ≈ y → f x ≡ f y)
    → _/≈ → B
  quot-rec = Q.quot-rec

  quot-rel : ∀ x y → x ≈ y → [ x ] ≡ [ y ]
  quot-rel = Q.quot-rel

  effectiveness : ∀ x y → [ x ] ≡ [ y ] → x ≈ y
  effectiveness x y p = unbox (≡.subst P p (box refl))
    where
    P : _/≈ → Set ℓR
    P = quot-rec (λ a → Box (x ≈ a)) λ a b a≈b →
          ≡.cong Box (propExt (x≈a⇔x≈b a≈b))
      where
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b = (λ x≈a → trans x≈a a≈b)
                  , (λ x≈b → trans x≈b (sym a≈b))

  quot-cong
    : ∀ {ℓB} {B : Set ℓB}
    → (f : _/≈ → B)
    → A → B
  quot-cong f x = f [ x ]
