open import QIT.Prelude

module QIT.Relation.SetQuotient ⦃ pathElim* : PathElim ⦄ where

open import QIT.Prelude
open import QIT.Prop

record SetQuotientStr {ℓA ℓR}
  (A : Set ℓA)
  (R : A → A → Prop ℓR)
  : Set (lsuc (ℓA ⊔ ℓR)) where
  field
    Q : Set (ℓA ⊔ ℓR)
    [_] : A → Q
    quot-rel : (x y : A) → R x y → _≡_ {A = Q} [ x ] [ y ]

record SetQuotientElimStr {ℓA ℓR}
  {A : Set ℓA}
  {R : A → A → Prop ℓR}
  (SQ : SetQuotientStr A R)
  (ℓB : Level)
  : Set (lsuc (ℓA ⊔ ℓR ⊔ ℓB)) where
  open SetQuotientStr SQ public

  field
    quot-elim : (B : Q → Set ℓB)
      → (f : ∀ a → B [ a ])
      → (eq : (x y : A) → (r : R x y) → subst B (quot-rel x y r) (f x) ≡ f y)
      → ∀ q → B q

    quot-elim-beta : (B : Q → Set ℓB)
      → (f : ∀ a → B [ a ])
      → (eq : (x y : A) → (r : R x y) → subst B (quot-rel x y r) (f x) ≡ f y)
      → (x : A)
      → quot-elim B f eq [ x ] ≡ f x

  quot-rec : {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ f y)
    → Q → B
  quot-rec {B} f eq =
    quot-elim (λ _ → B) f
      (λ x y r →
        ≡.trans (≡.subst-const B (f x) (quot-rel x y r))
          (eq x y r))

  quot-rec-beta : {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ f y)
    → (x : A)
    → quot-rec f eq [ x ] ≡ f x
  quot-rec-beta {B} f eq x =
    quot-elim-beta (λ _ → B) f
      (λ x y r →
        ≡.trans (≡.subst-const B (f x) (quot-rel x y r))
          (eq x y r))
      x

  quot-recp : {B : Prop ℓB}
    → (f : A → B)
    → Q → B
  quot-recp f q =
    unbox (quot-rec (λ x → box (f x)) (λ _ _ _ → ≡.isPropBox _ _) q)

  quot-elimp : (B : Q → Prop ℓB)
    → (f : ∀ a → B [ a ])
    → ∀ q → B q
  quot-elimp B f q =
    unbox (quot-elim (λ x → Box (B x)) (λ x → box (f x)) (λ _ _ _ → ≡.isPropBox _ _) q)


record SetQuotients : Agda.Primitive.Setω where
  field
    sq : ∀ {ℓA ℓR} (A : Set ℓA) (R : A → A → Prop ℓR) → SetQuotientStr A R
    sqe :
      ∀ {ℓA ℓR}
      → {A : Set ℓA}
      → {R : A → A → Prop ℓR}
      → (sq : SetQuotientStr A R)
      → (ℓB : Level)
      → SetQuotientElimStr sq ℓB

module _
  ⦃ sq* : SetQuotients ⦄
  where
  open SetQuotients sq*

  _/_ : ∀ {ℓA ℓR} → (A : Set ℓA) (R : A → A → Prop ℓR) → Set (ℓA ⊔ ℓR)
  A / R = SetQuotientStr.Q (sq A R)

  module SetQuotient {ℓA ℓR} {A : Set ℓA} {R : A → A → Prop ℓR}
    where

    open SetQuotientStr (sq A R) using ([_]; quot-rel) public
    {-# DISPLAY SetQuotientStr.[_] _ x = [ x ] #-}
    {-# DISPLAY SetQuotientStr.quot-rel _ x y r = quot-rel x y r #-}

    module _ {ℓB} where
      open SetQuotientElimStr (sqe (sq A R) ℓB) using ( quot-elim ; quot-elim-beta ; quot-rec
                                    ; quot-rec-beta ; quot-recp ; quot-elimp) public
      {-# DISPLAY SetQuotientElimStr.quot-elim _ B f eq q = quot-elim B f eq q #-}
      {-# DISPLAY SetQuotientElimStr.quot-elim-beta _ B f eq x = quot-elim-beta B f eq x #-}
      {-# DISPLAY SetQuotientElimStr.quot-rec _ f eq q = quot-rec f eq q #-}
      {-# DISPLAY SetQuotientElimStr.quot-rec-beta _ f eq x = quot-rec-beta f eq x #-}
      {-# DISPLAY SetQuotientElimStr.quot-recp _ f q = quot-recp f q #-}
      {-# DISPLAY SetQuotientElimStr.quot-elimp _ B f q = quot-elimp B f q #-}

  open SetQuotient public

  quot-drel : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} (B : A → Set ℓB) (R : ∀ {x} → B x → B x → Prop ℓR)
      → {x y : A} (u : B x) (v : B y) (p : x ≡ y)
      → R (subst B p u) v → ≡.subst (λ ○ → B ○ / R) p [ u ] ≡ [ v ]
  quot-drel B R u v ≡.refl ruv =
    ≡.trans (≡.subst-refl [ u ])
      (quot-rel u v (≡.substp (λ z → R z v) (≡.subst-refl u) ruv))

  -- {-# REWRITE quot-rec-beta #-}
  -- {-# REWRITE quot-elim-beta #-}
