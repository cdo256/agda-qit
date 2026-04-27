module QIT.Prop.Properties where

open import QIT.Prelude
open import QIT.Prop.Base
open import QIT.Prop.Logic
open import QIT.Prop.Path

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl


transport : ∀ {ℓA} {A A' : Set ℓA} → A ≡ A' → A → A'
transport = subst (λ x → x)

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

congp : ∀ {a b} {A : Prop a} {B : Set b} (f : A → B)
      → ∀ {x y} → f x ≡ f y
congp _ = refl

congp₂ : ∀ {a b c} {A : Prop a} {B : Prop b} {C : Set c} (f : A → B → C)
      → ∀ {a1 a2 b1 b2} → f a1 b1 ≡ f a2 b2
congp₂ _ = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
      → ∀ {a1 a2 b1 b2} → a1 ≡ a2 → b1 ≡ b2 → f a1 b1 ≡ f a2 b2
cong₂ f refl refl = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D)
      → ∀ {a1 a2 b1 b2 c1 c2} → a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → f a1 b1 c1 ≡ f a2 b2 c2
cong₃ f refl refl refl = refl

prop-subst : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Prop ℓB}
           → {x y : A} → (p : x ≡ y) → B x → B y
prop-subst refl x = x

subst-uip : ∀ {ℓ} {A : Set ℓ} {P : A → Set} {x : A} {p q : x ≡ x}
            (h : p ≡ᵖ q) (u : P x)
          → subst P p u ≡ subst P q u
subst-uip refl u = refl

module ≡-Reasoning {ℓ} {A : Set ℓ} where
  infix 1 begin_
  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin p = p

  infixr 2 step-≡
  step-≡ : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ q p = trans p q
  syntax step-≡ x q p = x ≡⟨ p ⟩ q

  infix 3 _∎
  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl

subst-subst : ∀ {ℓA ℓP} {A : Set ℓA} {P : A → Set ℓP} {x y z : A}
            → (x≡y : x ≡ y) {y≡z : y ≡ z} {p : P x}
            → subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
subst-subst refl = refl

dcong : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y}
      → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f refl = refl

dcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
       → f x₁ y₁ ≡ f x₂ y₂
dcong₂ f refl refl = refl

dsubst₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : A → Set ℓB} (C : ∀ a → B a → Set ℓC)
       → {a1 a2 : A} {b1 : B a1} {b2 : B a2}
       → (p : a1 ≡ a2) (q : subst B p b1 ≡ b2)
       → C a1 b1 → C a2 b2
dsubst₂ C {a1} {a2} {b1} {b2} p q x =
  transport (dcong₂ C p q) x


isPropBox : ∀ {ℓ} {P : Prop ℓ} (p q : Box P) → p ≡ q
isPropBox (box p) (box q) = r refl
  where
  r : p ≡ᵖ q → box p ≡ box q
  r refl = refl

funExt⁻ : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
        → f ≡ g → (∀ x → f x ≡ g x)
funExt⁻ refl _ = refl

-- Commutation of subst with function composition
subst-∘ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : B → Set ℓC}
        → (f : A → B) {x y : A} (p : x ≡ y) (z : C (f x))
        → subst C (cong f p) z ≡ subst (λ a → C (f a)) p z
subst-∘ f refl z = refl

drefl : ∀ {ℓA ℓB} {A : Set ℓA} (B : A → Set ℓB) {a : A} {b : B a}
      → subst B refl b ≡ b
drefl B = refl

dsym : ∀ {ℓA ℓB} {A : Set ℓA}
      → (B : A → Set ℓB) {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      → (p : a1 ≡ a2)
      → subst B p b1 ≡ b2
      → subst B (sym p) b2 ≡ b1
dsym B refl refl = refl

dtrans : ∀ {ℓA ℓB} {A : Set ℓA}
      → (B : A → Set ℓB) {a1 a2 a3 : A} {b1 : B a1} {b2 : B a2} {b3 : B a3}
      → (p : a1 ≡ a2) (q : a2 ≡ a3)
      → subst B p b1 ≡ b2
      → subst B q b2 ≡ b3
      → subst B (trans p q) b1 ≡ b3
dtrans B refl refl refl refl = refl
