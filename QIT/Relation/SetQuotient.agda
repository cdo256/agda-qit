module QIT.Relation.SetQuotient where

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
        ≡.trans (eq x y r)
          (≡.sym (≡.subst-const B (f y) (quot-rel x y r))))

  quot-rec-beta : {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ f y)
    → (x : A)
    → quot-rec f eq [ x ] ≡ f x
  quot-rec-beta {B} f eq x =
    quot-elim-beta (λ _ → B) f
      (λ x y r →
        ≡.trans (eq x y r)
          (≡.sym (≡.subst-const B (f y) (quot-rel x y r))))
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


SetQuotients : Agda.Primitive.Setω
SetQuotients = ∀ {ℓA ℓR} (A : Set ℓA) (R : A → A → Prop ℓR) → SetQuotientStr A R
SetQuotientsElim : Agda.Primitive.Setω
SetQuotientsElim = 
  ∀ {ℓA ℓR}
  → {A : Set ℓA}
  → {R : A → A → Prop ℓR}
  → (sq : SetQuotientStr A R)
  → (ℓB : Level)
  → SetQuotientElimStr sq ℓB

module WithSetQuotients
  (sq : SetQuotients)
  (sqe : SetQuotientsElim)
  where

  _/_ : ∀ {ℓA ℓR} → (A : Set ℓA) (R : A → A → Prop ℓR) → Set (ℓA ⊔ ℓR)
  A / R = SetQuotientStr.Q (sq A R)

  module SetQuotient {ℓA ℓR} {A : Set ℓA} {R : A → A → Prop ℓR}
    where

    open SetQuotientStr (sq A R) using ([_]; quot-rel) public
    module _ {ℓB} where
      open SetQuotientElimStr (sqe (sq A R) ℓB) using ( quot-elim ; quot-elim-beta ; quot-rec
                                    ; quot-rec-beta ; quot-recp ; quot-elimp) public

  open SetQuotient public

  quot-drel : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} (B : A → Set ℓB) (R : ∀ {x} → B x → B x → Prop ℓR)
      → {x y : A} (u : B x) (v : B y) (p : x ≡ y)
      → R (subst B p u) v → ≡.subst (λ ○ → B ○ / R) p [ u ] ≡ [ v ]
  quot-drel B R u v ≡.refl ruv = quot-rel u v ruv

  -- {-# REWRITE quot-rec-beta #-}
  -- {-# REWRITE quot-elim-beta #-}
