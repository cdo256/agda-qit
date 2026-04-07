open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
open import QIT.Setoid.Base
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

  quot-rec
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : {x y : A} → x ≈ y → f x ≡ f y)
    → Ã /≈ → B
  quot-rec f eq = Q.quot-rec f λ _ _ → eq

  quot-elim
    : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : {x y : A} → (r : x ≈ y) → subst B ≈[ r ] (f x) ≡ (f y))
    → ∀ a/ → B a/
  quot-elim B f eq = Q.quot-elim B f λ _ _ → eq

  quot-recp : ∀ {ℓB} {B : Prop ℓB}
    → (f : A → B)
    → Ã /≈ → B
  quot-recp f x = Q.quot-recp f x

  quot-elimp : ∀ {ℓB} (B : Ã /≈ → Prop ℓB)
    → (f : ∀ a → B [ a ])
    → ∀ a/ → B a/
  quot-elimp B f a/ = Q.quot-elimp B f a/

  effectiveness : ∀ x y → [ x ] ≡ [ y ] → x ≈ y
  effectiveness x y p = unbox (≡.subst P p (box refl))
    where
    P : Ã /≈ → Set ℓR
    P = quot-rec
          (λ a → Box (x ≈ a))
          (λ a≈b → ≡.cong Box (propExt (x≈a⇔x≈b a≈b)))
      where
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b = (λ x≈a → trans x≈a a≈b)
                  , (λ x≈b → trans x≈b (sym a≈b))

  quot-cong
    : ∀ {ℓB} {B : Set ℓB}
    → (f : Ã /≈ → B)
    → A → B
  quot-cong f x = f [ x ]

  quot-rec-beta
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : {x y : A} → x ≈ y → f x ≡ f y) (x : A)
    → quot-rec f eq [ x ] ≡ f x
  quot-rec-beta f eq x = Q.quot-rec-beta f (λ _ _ → eq) x

  quot-elim-beta
    : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : {x y : A} → (r : x ≈ y) → subst B ≈[ r ] (f x) ≡ (f y))
    → (x : A)
    → quot-elim B f eq [ x ] ≡ f x
  quot-elim-beta B f eq x = Q.quot-elim-beta B f (λ _ _ → eq) x
