open import QIT.Prelude

module QIT.Identity where

open import QIT.Prelude.Identity public

postulate
  funExt : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
          → (∀ x → f x ≡ g x) → f ≡ g
  subst : ∀ {ℓA ℓB} {A : Set ℓA} (B : A → Set ℓB) {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
  subst-id : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
           → {x : A} (p : x ≡ x) (b : B x)
           → subst B p b ≡ b
  subst-const : ∀ {ℓA ℓB} {A : Set ℓA} (B : Set ℓB)
              → ∀ {x y : A} (z : B) (p : x ≡ y)
              → subst (λ _ → B) p z ≡ z
  J : ∀ {ℓA ℓB} {A : Set ℓA} {x : A}
    → (B : (y : A) → x ≡ y → Set ℓB)
    → {y : A} (p : x ≡ y) → B x refl → B y p

{-# REWRITE subst-id #-}
{-# REWRITE subst-const #-}

Jp : ∀ {ℓA ℓB} {A : Set ℓA} {x : A} → (B : (y : A) → x ≡ y → Prop ℓB)
  → {y : A} (p : x ≡ y) → B x refl → B y p
Jp B refl x = x


≡ˢ→≡ : ∀ {ℓA} {A : Set ℓA} {x y : A} → x ≡ˢ y → x ≡ y
≡ˢ→≡ reflˢ = refl

≡→≡ˢ : ∀ {ℓA} {A : Set ℓA} {x y : A} → x ≡ y → x ≡ˢ y
≡→≡ˢ {x = x} {y} p = J (λ y p → x ≡ˢ y) p reflˢ

ΣP≡' : ∀ {a b} {A : Set a} {B : A → Prop b}
    → (a1 a2 : A) → a1 ≡ a2
    → ∀ (b1 : B a1) (b2 : B a2)
    → _≡_ {A = ΣP A B} (a1 , b1) (a2 , b2)
ΣP≡' {a} {b} {A = A} {B = B} a1 a2 p = Jp C p λ b1 b2 → refl
  where
  C : ∀ a2 → a1 ≡ a2 → Prop (a ⊔ b)
  C a2 p = ∀ (b1 : B a1) (b2 : B a2)
         → _≡_ {A = ΣP A B} (a1 , b1) (a2 , b2)

ΣP≡ : ∀ {a b} {A : Set a} {B : A → Prop b}
    → (x y : ΣP A B) → x .fst ≡ y .fst → x ≡ y
ΣP≡ x y p = ΣP≡' (x .fst) (y .fst) p (x .snd) (y .snd)

substΣP : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
        → {a1 a2 : A} (p : a1 ≡ a2) (b : B a1) → Σ A B
substΣP {B = B} {a2 = a2} p b = a2 , subst B p b

subst-Π : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Set ℓC)
        → {x y : A} (p : x ≡ y)
        → (g : ∀ z → C x z)
        → (z : B)
        → subst (λ a → ∀ b → C a b) p g z
        ≡ subst (λ a → C a z) p (g z)
subst-Π {A = A} {B} C {x} p =
  Jp (λ _ p → (g : ∀ b → C x b) (z : B)
            → subst (λ a → ∀ b → C a b) p g z
            ≡ subst (λ a → C a z) p (g z))
     p (λ _ _ → refl)
