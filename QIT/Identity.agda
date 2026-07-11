open import QIT.Prelude

module QIT.Identity ⦃ pathElim* : PathElim ⦄ where

module PE = PathElim pathElim*

open import QIT.Prelude.Identity public

abstract
  J : ∀ {ℓA ℓB} {A : Set ℓA} {x : A}
    → (B : (y : A) → x ≡ y → Set ℓB)
    → {y : A} (p : x ≡ y) → B x refl → B y p
  J = PE.J
  J-refl : ∀ {ℓA ℓB} {A : Set ℓA} {x : A}
          → (B : (y : A) → x ≡ y → Set ℓB)
          → (Brefl : B x refl)
          → J B refl Brefl ≡ Brefl
  J-refl = PE.J-refl
{-# REWRITE J-refl #-}

isSetSetˢ : {A : Set ℓA} {x y : A} (p q : x ≡ˢ y) → p ≡ˢ q
isSetSetˢ reflˢ reflˢ = reflˢ

isSetSetˢᵖ : {A : Set ℓA} {x y : A} (p q : x ≡ˢ y) → p ≡ q
isSetSetˢᵖ reflˢ reflˢ = refl

≡ˢ→≡ : {A : Set ℓA} {x y : A} → x ≡ˢ y → x ≡ y
≡ˢ→≡ reflˢ = refl

≡→≡ˢ : {A : Set ℓA} {x y : A} → x ≡ y → x ≡ˢ y
≡→≡ˢ {x = x} {y = y} p = J (λ y p → x ≡ˢ y) p reflˢ

Jˢ : {A : Set ℓA} {x : A}
    → (B : (y : A) → x ≡ˢ y → Set ℓB)
    → {y : A} (p : x ≡ˢ y) → B x reflˢ → B y p
Jˢ B reflˢ Brefl = Brefl

Jp : ∀ {ℓA ℓB} {A : Set ℓA} {x : A} → (B : (y : A) → x ≡ y → Prop ℓB)
  → {y : A} (p : x ≡ y) → B x refl → B y p
Jp B refl x = x

Jˢ-refl : {A : Set ℓA} {x : A}
      → (B : (y : A) → x ≡ˢ y → Set ℓB)
      → (Brefl : B x reflˢ)
      → Jˢ B reflˢ Brefl ≡ˢ Brefl
Jˢ-refl B Brefl = reflˢ

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

transport : ∀ {ℓA} {A A' : Set ℓA} → A ≡ A' → A → A'
transport = J (λ X _ → X)

subst : {A : Set ℓA} (B : A → Set ℓB) {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
subst B = J (λ v _ → B v)

substp : {A : Set ℓA} (B : A → Prop ℓB) {a1 a2 : A} (p : a1 ≡ a2) → B a1 → B a2
substp B = Jp (λ v _ → B v)

transportp : {A A' : Prop ℓA} (p : A ≡ A') → A → A'
transportp = Jp (λ v _ → v)

substp' : {A : Prop ℓA} (B : A → Prop ℓB) {a1 a2 : A} → B a1 → B a2
substp' B x = x

subst-id : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
          → {x : A} (p : x ≡ x) (b : B x)
          → subst B p b ≡ b
subst-id {B = B} refl b = refl

subst-refl : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
          → {x : A} (b : B x)
          → subst B refl b ≡ b
subst-refl {B = B} b = refl

subst-irrel : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
          → {x y : A} (p q : x ≡ y) (b : B x)
          → subst B p b ≡ subst B q b
subst-irrel {B = B} refl refl b = refl

subst-const : ∀ {ℓA ℓB} {A : Set ℓA} (B : Set ℓB)
            → ∀ {x y : A} (z : B) (p : x ≡ y)
            → subst (λ _ → B) p z ≡ z
subst-const B z refl = refl

subst₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Set ℓC)
       → {a1 a2 : A} {b1 b2 : B}
       → (p : a1 ≡ a2) (q : b1 ≡ b2)
       → C a1 b1 → C a2 b2
subst₂ C {a1} {a2} {b1} {b2} p q x =
  subst (λ ○ → C ○ b2) p
    (subst (C a1) q x)

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

subst-uip : {A : Set ℓA} {B : A → Set ℓB}
          → {x : A} {p q : x ≡ x} (u : B x)
          → subst B p u ≡ subst B q u
subst-uip u = refl

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
subst-subst P refl refl p =
  refl

subst-inv : ∀ {ℓA ℓP} {A : Set ℓA} (P : A → Set ℓP) {x y : A}
            → (p : x ≡ y) {u : P x}
            → subst P (sym p) (subst P p u) ≡ u
subst-inv P refl {u} =
  subst-subst P refl refl u

dcong : {A : Set ℓA} {B : A → Set ℓB} (f : (x : A) → B x)
      → ∀ {x y} → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f {x = x} refl = refl

dcong₂ : {A : Set ℓA} {B : A → Set ℓB} {C : Set ℓC}
         (f : (x : A) → B x → C) → ∀ {x₁ x₂ y₁ y₂}
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
dsubst₂ C p q x =
  transport (dcong₂ C p q) x

dsubstp₂ : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : A → Set ℓB} (C : ∀ a → B a → Prop ℓC)
       → {a1 a2 : A} {b1 : B a1} {b2 : B a2}
       → (p : a1 ≡ a2) (q : subst B p b1 ≡ b2)
       → C a1 b1 → C a2 b2
dsubstp₂ C refl refl x = x

isPropBox : ∀ {ℓ} {P : Prop ℓ} (p q : Box P) → p ≡ q
isPropBox (box p) (box q) = refl

funExt⁻ : ∀ {ℓA ℓB} → {A : Set ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
       → f ≡ g → (∀ x → f x ≡ g x)
funExt⁻ refl _ = refl

funExtp⁻ : ∀ {ℓA ℓB} → {A : Prop ℓA} {B : A → Set ℓB} {f g : ∀ x → B x}
       → f ≡ g → (∀ x → f x ≡ g x)
funExtp⁻ refl _ = refl

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
dsym B refl refl = subst-inv B refl

dtrans : ∀ {ℓA ℓB} {A : Set ℓA}
      → (B : A → Set ℓB) {a1 a2 a3 : A} {b1 : B a1} {b2 : B a2} {b3 : B a3}
      → (p : a1 ≡ a2) (q : a2 ≡ a3)
      → subst B p b1 ≡ b2
      → subst B q b2 ≡ b3
      → subst B (trans p q) b1 ≡ b3
dtrans B refl refl refl refl = sym (subst-inv B refl)

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

substΣP : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
        → {a1 a2 : A} (p : a1 ≡ a2) (b : B a1) → Σ A B
substΣP {B = B} {a2 = a2} p b = a2 , subst B p b

subst-ΣP : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : A → Set ℓB} (C : ∀ a → B a → Prop ℓC)
         → {a1 a2 : A} (p : a1 ≡ a2) (u : ΣP (B a1) (C a1))
         → subst (λ a → ΣP (B a) (C a)) p u
         ≡ (subst B p (u .fst) , dsubstp₂ C p refl (u .snd))
subst-ΣP C refl (x , y) = refl

subst-Π : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : A → B → Set ℓC)
        → {x y : A} (p : x ≡ y)
        → (g : ∀ z → C x z)
        → (z : B)
        → subst (λ a → ∀ b → C a b) p g z
        ≡ subst (λ a → C a z) p (g z)
subst-Π {A = A} {B} C {x} refl g z = refl

-- dfunExt
--   : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : A → Set ℓB}
--   → (C : ∀ a → B a → Set ℓC)
--   → {x y : A} (p : x ≡ y)
--   → {f : ∀ b → C x b} {g : ∀ b → C y b}
--   → (∀ a → (q : a ≡ x) → (b : B a)
--          → subst (λ a → C a {! b!}) p {!f b!}
--                ≡ {!g (subst B p b)!})
--   → subst (λ a → ∀ b → C a b) p f ≡ g
-- dfunExt C refl h = {!!}


subst-cong
  : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} (C : B → Set ℓC)
  → (f : A → B)
  → {x y : A} (p : x ≡ y)
  → (c : C (f x))
  → subst (λ x → C (f x)) p c
  ≡ subst C (cong f p) c
subst-cong C f refl c = refl
