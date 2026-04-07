module QIT.Relation.SetQuotient where

open import QIT.Prelude
open import QIT.Prop

postulate
  _/_ : ∀ {ℓA ℓR} → (A : Set ℓA) (R : A → A → Prop ℓR) → Set (ℓA ⊔ ℓR)
  [_] : ∀ {ℓA ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} → A → A / R
  quot-rec : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ f y)
    → A / R → B

  quot-rec-beta
    : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ f y) (x : A)
    → quot-rec f eq [ x ] ≡ f x

  quot-rel : ∀ {ℓA ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} (x y : A)
    → R x y → _≡_ {A = A / R} [ x ] [ y ]

  -- Probably doesn't need to be postulated.
  quot-elim : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : A / R → Set ℓB}
    → (f : ∀ a → B [ a ])
    → (eq : (x y : A) → (r : R x y) → subst B (quot-rel x y r) (f x) ≡ (f y))
    → ∀ a/ → B a/

quot-recp : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Prop ℓB}
  → (f : A → B)
  → A / R → B
quot-recp f x = unbox (quot-rec (λ x → box (f x)) (λ _ _ _ → ≡.isPropBox _ _) x)


quot-elimp : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : A / R → Prop ℓB}
  → (f : ∀ a → B [ a ])
  → ∀ a/ → B a/
quot-elimp f a/ = unbox (quot-elim (λ x → box (f x)) (λ _ _ _ → ≡.isPropBox _ _) a/)

{-# REWRITE quot-rec-beta #-}

