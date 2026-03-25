module QIT.Prop.Properties where

open import QIT.Prelude
open import QIT.Prop.Base
open import QIT.Prop.Logic
open import QIT.Prop.Path

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Set ℓC)
       → {a1 a2 : A} {b1 b2 : B}
       → (p : a1 ≡ a2) (q : b1 ≡ b2)
       → C a1 b1 → C a2 b2
subst₂ C {a1} {a2} {b1} {b2} p q x =
  subst (λ ○ → C ○ b2) p
    (subst (C a1) q x)

-- substp for Prop-valued families can pattern match on refl
substp : ∀ {ℓA ℓB} {A : Set ℓA} (B : A → Prop ℓB)
       → {a1 a2 : A} (p : a1 ≡ a2)
       → B a1 → B a2
substp B refl x = x

substp₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Prop ℓC)
       → {a1 a2 : A} {b1 b2 : B}
       → (p : a1 ≡ a2) (q : b1 ≡ b2)
       → C a1 b1 → C a2 b2
substp₂ C {a1} {a2} {b1} {b2} p q x =
  substp (λ ○ → C ○ b2) p
    (substp (C a1) q x)



-- substp for Set-valued families that return Props (like equivalence relations)
substp-Set : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (C : B → Prop ℓA)
           → {b1 b2 : B} (p : b1 ≡ b2)
           → C b1 → C b2
substp-Set C refl x = x

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
      → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

substDefEq : ∀ {ℓA ℓP} {A : Set ℓA} (P : A → Set ℓP)
           → ∀ {x} (p : x ≡ x) (y : P x) → subst P p y ≡ y
substDefEq P = subst-id

data _≡ᵖ_ {ℓA} {A : Prop ℓA} (x y : A) : Prop (lsuc ℓA) where
   refl : ∀ {x} → x ≡ᵖ y

prop-subst : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Prop ℓB}
           → {x y : A} → (p : x ≡ y) → B x → B y
prop-subst refl x = x

subst-uip : ∀ {ℓ} {A : Set ℓ} {P : A → Set} {x : A} {p q : x ≡ x}
            (h : p ≡ᵖ q) (u : P x)
          → subst P p u ≡ subst P q u
subst-uip refl u = refl

isPropBox : ∀ {ℓ} {P : Prop ℓ} (p q : Box P) → p ≡ q
isPropBox (box p) (box q) = r refl
  where
  r : p ≡ᵖ q → box p ≡ box q
  r refl = refl
