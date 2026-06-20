open import QIT.Prelude

module QIT.Identity where

open import QIT.Prelude
open import QIT.Logic

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

Σ≡ : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB}
   → {a1 a2 : A} {b1 : B a1} {b2 : B a2}
   → (p : a1 ≡ a2) (q : subst B p b1 ≡ b2)
   → _≡_ {A = Σ A B} (a1 , b1) (a2 , b2)
Σ≡ refl refl = refl

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

subst-subst : ∀ {ℓA ℓP} {A : Set ℓA} (P : A → Set ℓP) {x y z : A}
            → (x≡y : x ≡ y) (y≡z : y ≡ z) (p : P x)
            → subst P y≡z (subst P x≡y p) ≡ subst P (trans x≡y y≡z) p
subst-subst P refl refl p = refl

subst-inv : ∀ {ℓA ℓP} {A : Set ℓA} (P : A → Set ℓP) {x y : A}
            → (p : x ≡ y) {u : P x}
            → subst P (sym p) (subst P p u) ≡ u
subst-inv P refl = refl

dcong : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y}
      → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f refl = refl

dcong₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
       → f x₁ y₁ ≡ f x₂ y₂
dcong₂ f refl refl = refl

dcongsp : ∀ {a b c} {A : Set a} {B : A → Prop b} {C : Set c}
         (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
       → (p : x₁ ≡ x₂)
       → f x₁ y₁ ≡ f x₂ y₂
dcongsp f refl = refl


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

≡→⇔ : ∀ {ℓA} {A B : Prop ℓA} → A ≡ B → A ⇔ B
≡→⇔ {A = A} p = substp (A ⇔_) p ⇔refl

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

subst-cong
  : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : B → Set ℓC)
  → (f : A → B)
  → {x y : A} (p : x ≡ y)
  → (c : C (f x))
  → subst (λ x → C (f x)) p c
  ≡ subst C (cong f p) c
subst-cong C f {x} {y} p c = Jp Q p refl
  where
  Q : ∀ y (p : x ≡ y) → Prop _
  Q _ p = subst (λ x → C (f x)) p c
        ≡ subst C (cong f p) c
