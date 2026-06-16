module QIT.Relation.SetQuotient where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary
open import QIT.Relation.Nullary

postulate
  _/_ : ∀ {ℓA ℓR} → (A : Set ℓA) (R : A → A → Prop ℓR) → Set (ℓA ⊔ ℓR)
  [_] : ∀ {ℓA ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} → A → A / R

  quot-rel : ∀ {ℓA ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} (x y : A)
    → R x y → _≡ˢ_ {A = A / R} [ x ] [ y ]

  quot-rec : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ˢ f y)
    → A / R → B

  -- Probably doesn't need to be postulated.
  quot-elim : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} (B : A / R → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : (x y : A) → (r : R x y) → substˢ B (quot-rel x y r) (f x) ≡ˢ (f y))
    → ∀ a/ → B a/

  quot-rec-beta
    : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Set ℓB}
    → (f : A → B)
    → (eq : (x y : A) → R x y → f x ≡ˢ f y) (x : A)
    → quot-rec f eq [ x ] ≡ˢ f x

  quot-elim-beta
    : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} (B : A / R → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : (x y : A) → (r : R x y) → substˢ B (quot-rel x y r) (f x) ≡ˢ (f y))
    → (x : A)
    → quot-elim B f eq [ x ] ≡ˢ f x

quot-recp : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Prop ℓB}
  → (f : A → B)
  → A / R → B
quot-recp f x = unbox (quot-rec (λ x → box (f x)) (λ _ _ _ → ≡.isPropBoxˢ _ _) x)

quot-elimp : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} (B : A / R → Prop ℓB)
  → (f : ∀ a → B [ a ])
  → ∀ a/ → B a/
quot-elimp B f a/ =
  unbox (quot-elim (λ x → Box (B x)) (λ x → box (f x)) (λ _ _ _ → ≡.isPropBoxˢ _ _) a/)

quot-rec₂ : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Set ℓB}
  → IsEquivalence R
  → (f : A → A → B)
  → (eq : {x₁ x₂ y₁ y₂ : A} → R x₁ y₁ → R x₂ y₂ → f x₁ x₂ ≡ˢ f y₁ y₂)
  → A / R → A / R → B
quot-rec₂ {A = A} {R} {B} equivR f eq =
  quot-rec g g-cong
  where
  open IsEquivalence equivR
  g : A → A / R → B
  g x = quot-rec (f x) λ y z p → eq refl p
  g-cong : ∀ x y → R x y → g x ≡ˢ g y
  g-cong x y p = funExtˢ (quot-elim B' r u)
    where
    B' : (z : A / R) → Set _
    B' z = quot-rec (f x) (λ _ _ → eq refl) z ≡ˢ quot-rec (f y) (λ _ _ → eq refl) z
    r : (a : A) → B' [ a ]
    r a = transˢ (quot-rec-beta (f x) (λ _ _ → eq _) a)
          (transˢ (eq p refl) (symˢ (quot-rec-beta (f y) (λ _ _ → eq _) a))) 
    u : ∀ (x' y' : A) (rxy : R x' y') →
         substˢ B' (quot-rel x' y' rxy) (r x') ≡ˢ r y'
    u x' y' rxy = ≡→≡ˢ (isSetSetˢ _ _)

quot-rec₂-beta : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} {B : Set ℓB}
  → (equivR : IsEquivalence R)
  → (f : A → A → B)
  → (eq : {x₁ x₂ y₁ y₂ : A} → R x₁ y₁ → R x₂ y₂ → f x₁ x₂ ≡ˢ f y₁ y₂)
  → (x z : A)
  → quot-rec₂ equivR f eq [ x ] [ z ] ≡ˢ f x z
quot-rec₂-beta {A = A} {R} {B = B} equivR f eq x z =
  transˢ (congˢ (λ h → h [ z ]) (quot-rec-beta g g-cong x))
         (quot-rec-beta (f x) (λ _ _ p → eq (IsEquivalence.refl equivR) p) z)
  where
  g : A → A / R → B
  g x = quot-rec (f x) λ _ _ p → eq (IsEquivalence.refl equivR) p

  g-cong : ∀ x y → R x y → g x ≡ˢ g y
  g-cong x y p = funExtˢ (quot-elim B' r u)
    where
    B' : (q : A / R) → Set _
    B' q = g x q ≡ˢ g y q

    r : ∀ a → B' [ a ]
    r a = transˢ (quot-rec-beta (f x) (λ _ _ s → eq (IsEquivalence.refl equivR) s) a)
           (transˢ (eq p (IsEquivalence.refl equivR))
                   (symˢ (quot-rec-beta (f y) (λ _ _ s → eq (IsEquivalence.refl equivR) s) a)))

    u : ∀ x' y' (rxy : R x' y') → substˢ B' (quot-rel x' y' rxy) (r x') ≡ˢ r y'
    u x' y' rxy = ≡→≡ˢ (isSetSetˢ _ _)

quot-drel : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} (B : A → Set ℓB) (R : ∀ {x} → B x → B x → Prop ℓR)
    → {x y : A} (u : B x) (v : B y) (p : x ≡ˢ y)
    → R (substˢ B p u) v → substˢ (λ ○ → B ○ / R) p [ u ] ≡ˢ [ v ]
quot-drel B R u v reflˢ ruv = quot-rel u v ruv

-- quot-rec₂
--     : ∀ {ℓB} {B : Set ℓB}
--     → (f : A → A → B)
--     → (eq : {x y z w : A} → x ≈ y → z ≈ w → f x z ≡ˢ f y w)
--     → Ã /≈ → Ã /≈ → B
-- rec₂ {B = B} f eq = rec g g-cong
--     where
--     g : A → Ã /≈ → B
--     g x = rec (f x) (eq refl)
--     g-cong : ∀ {x y} → x ≈ y → g x ≡ g y
--     g-cong {x} {y} p =
--       ≡.funExt (Q.quot-elimp
--         (λ z → rec (f x) (eq refl) z ≡ rec (f y) (eq refl) z)
--         (λ a → eq p refl))

-- quot-elimp : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} {R : A → A → Prop ℓR} (B : A / R → Prop ℓB)
--   → (f : ∀ a → B [ a ])
--   → ∀ a/ → B a/
-- quot-elimp B f a/ = unbox (quot-elim (λ x → Box (B x)) (λ x → box (f x)) (λ _ _ _ → ≡.isPropBoxˢ _ _) a/)

-- quot-drel : ∀ {ℓA ℓB ℓR} → {A : Set ℓA} (B : A → Set ℓB) (R : ∀ {x} → B x → B x → Prop ℓR)
--     → {x y : A} (u : B x) (v : B y) (p : x ≡ˢ y)
--     → R (substˢ B p u) v → substˢ (λ ○ → B ○ / R) p [ u ] ≡ˢ [ v ]
-- quot-drel B R u v ≡.reflˢ ruv = quot-rel u v ruv

-- -- TODO: No rewriting for ≡ˢ yet.
-- -- {-# REWRITE quot-rec-beta #-}
-- -- {-# REWRITE quot-elim-beta #-}
