open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Properties using (isPropBox)
open import QIT.Prop.Logic
open import QIT.Setoid.Base renaming (_[_≈_] to _⟦_≈_⟧)
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
  ≈[_] p = ≡ˢ→≡ (Q.quot-rel _ _ p)

  rec
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : {x y : A} → x ≈ y → f x ≡ f y)
    → Ã /≈ → B
  rec f eq = Q.quot-rec f λ _ _ r → ≡→≡ˢ (eq r)

  rec₂
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → A → B)
    → (eq : {x y z w : A} → x ≈ y → z ≈ w → f x z ≡ f y w)
    → Ã /≈ → Ã /≈ → B
  rec₂ f eq = Q.quot-rec₂ isEquivalence f λ p q → ≡→≡ˢ (eq p q)

  elim
    : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : {x y : A} → (r : x ≈ y) → substˢ B (Q.quot-rel x y r) (f x) ≡ f y)
    → ∀ a/ → B a/
  elim B f eq = Q.quot-elim B f λ _ _ r → ≡→≡ˢ (eq r)

  recp : ∀ {ℓB} {B : Prop ℓB}
    → (f : A → B)
    → Ã /≈ → B
  recp f x = Q.quot-recp f x

  recp₂
    : ∀ {ℓB} {B : Prop ℓB}
    → (f : A → A → B)
    → Ã /≈ → Ã /≈ → B
  recp₂ {B = B} f x y = unbox (rec₂ (λ x y → box (f x y)) (λ _ _ → isPropBox _ _) x y)

  elimp : ∀ {ℓB} (B : Ã /≈ → Prop ℓB)
    → (f : ∀ a → B [ a ])
    → ∀ a/ → B a/
  elimp B f a/ = Q.quot-elimp B f a/

  elimp₂
    : ∀ {ℓB} {B : Ã /≈ → Ã /≈ → Prop ℓB}
    → (f : ∀ x y → B [ x ] [ y ])
    → ∀ x y → B x y
  elimp₂ {B = B} f x y =
    elimp (λ a/ → ∀ b/ → B a/ b/)
          (λ a → elimp (B [ a ]) (f a)) x y


  effectiveness : ∀ x y → [ x ] ≡ [ y ] → x ≈ y
  effectiveness x y p = unbox py
    where
    P : Ã /≈ → Set ℓR
    P = rec
          (λ a → Box (x ≈ a))
          (λ a≈b → ≡.cong Box (propExt (x≈a⇔x≈b a≈b)))
      where
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b = (λ x≈a → trans x≈a a≈b)
                  , (λ x≈b → trans x≈b (sym a≈b))

    βx : P [ x ] ≡ˢ Box (x ≈ x)
    βx = Q.quot-rec-beta (λ a → Box (x ≈ a))
           (λ _ _ a≈b → ≡→≡ˢ (≡.cong Box (propExt (x≈a⇔x≈b a≈b)))) x
      where
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b = (λ x≈a → trans x≈a a≈b)
                  , (λ x≈b → trans x≈b (sym a≈b))

    px : P [ x ]
    px = ≡.transport (≡ˢ→≡ (symˢ βx)) (box refl)

    βy : P [ y ] ≡ˢ Box (x ≈ y)
    βy = Q.quot-rec-beta (λ a → Box (x ≈ a))
           (λ _ _ a≈b → ≡→≡ˢ (≡.cong Box (propExt (x≈a⇔x≈b a≈b)))) y
      where
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b = (λ x≈a → trans x≈a a≈b)
                  , (λ x≈b → trans x≈b (sym a≈b))

    py : Box (x ≈ y)
    py = ≡.transport (≡ˢ→≡ βy) (≡.subst P p px)

  cong
    : ∀ {ℓB} {B : Set ℓB}
    → (f : Ã /≈ → B)
    → A → B
  cong f x = f [ x ]

  rec-beta
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → B)
    → (eq : {x y : A} → x ≈ y → f x ≡ f y) (x : A)
    → rec f eq [ x ] ≡ f x
  rec-beta f eq x = ≡ˢ→≡ (Q.quot-rec-beta f (λ _ _ p → ≡→≡ˢ (eq p)) x)

  rec₂-beta
    : ∀ {ℓB} {B : Set ℓB}
    → (f : A → A → B)
    → (eq : {x y z w : A} → x ≈ y → z ≈ w → f x z ≡ f y w) (x z : A)
    → rec₂ f eq [ x ] [ z ] ≡ f x z
  rec₂-beta f eq x z =
    ≡ˢ→≡ (Q.quot-rec₂-beta isEquivalence f (λ p q → ≡→≡ˢ (eq p q)) x z)

  elim-beta
    : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
    → (f : ∀ a → B [ a ])
    → (eq : {x y : A} → (r : x ≈ y) → substˢ B (Q.quot-rel x y r) (f x) ≡ f y)
    → (x : A)
    → elim B f eq [ x ] ≡ f x
  elim-beta B f eq x = ≡ˢ→≡ (Q.quot-elim-beta B f (λ _ _ r → ≡→≡ˢ (eq r)) x)

  postulate
    elim₂
      : ∀ {ℓX} (X : Ã /≈ → Ã /≈ → Set ℓX)
      → (f : ∀ a b → X [ a ] [ b ])
      → (eq : ∀ {x y z w} (r : x ≈ y) (s : z ≈ w)
            → substˢ (X [ y ]) (Q.quot-rel z w s)
                (substˢ (λ a/ → X a/ [ z ]) (Q.quot-rel x y r) (f x z))
              ≡ f y w)
      → ∀ a/ b/ → X a/ b/

  map : ∀ {ℓB ℓS} (B̃ : Setoid ℓB ℓS) (f₀ : ⟨ Ã ⟩ → ⟨ B̃ ⟩) (f-cong : ∀ {x y : ⟨ Ã ⟩} → x ≈ y → B̃ ⟦ f₀ x ≈ f₀ y ⟧) → Ã /≈ → B̃ /≈
  map B̃ f₀ f-cong = rec (λ x → Q.[ f₀ x ]) λ {x} {y} p → ≡ˢ→≡ (Q.quot-rel (f₀ x) (f₀ y) (f-cong p))
    where
    module B = Setoid B̃

open SetoidQuotient using () renaming ([_] to _⊢[_]; ≈[_] to _⊢≈[_]) public

record QuotRelWitness {ℓA ℓA≈ ℓB ℓB≈ ℓR} (A : Setoid ℓA ℓA≈) (B : Setoid ℓB ℓB≈)
        (R : ⟨ A ⟩ → ⟨ B ⟩ → Prop ℓR)
        (a : A /≈) (b : B /≈) : Set (ℓA ⊔ ℓA≈ ⊔ ℓB ⊔ ℓB≈ ⊔ ℓR) where
  constructor qrwitness
  field
    a₀ : ⟨ A ⟩
    b₀ : ⟨ B ⟩
    r : R a₀ b₀
    pa : A ⊢[ a₀ ] ≡ a
    pb : B ⊢[ b₀ ] ≡ b
    
QuotHetRel∀ : ∀ {ℓA ℓB ℓB≈ ℓR} {A : Set ℓA} (B : A → Setoid ℓB ℓB≈)
        → (R : ∀ {x y} → ⟨ B x ⟩ → ⟨ B y ⟩ → Prop ℓR)
        → (∀ {x y} → B x /≈ → B y /≈ → Prop (ℓB ⊔ ℓB≈ ⊔ ℓR))
QuotHetRel∀ B R {x} {y} bx by =
  ∀ bx₀ by₀ → (B x ⊢[ bx₀ ] ≡ bx) → (B y ⊢[ by₀ ] ≡ by) → R bx₀ by₀
    
QuotHetRel∃ : ∀ {ℓA ℓB ℓB≈ ℓR} {A : Set ℓA} (B : A → Setoid ℓB ℓB≈)
        → (R : ∀ {x y} → ⟨ B x ⟩ → ⟨ B y ⟩ → Prop ℓR)
        → (∀ {x y} → B x /≈ → B y /≈ → Prop (ℓB ⊔ ℓB≈ ⊔ ℓR))
QuotHetRel∃ B R {x} {y} bx by = ∥ QuotRelWitness (B x) (B y) R bx by ∥

QuotHetRel∀→∃ : ∀ {ℓA ℓB ℓB≈ ℓR} {A : Set ℓA} (B : A → Setoid ℓB ℓB≈)
        → (R : ∀ {x y} → ⟨ B x ⟩ → ⟨ B y ⟩ → Prop ℓR)
        → ∀ {x y} → (bx : B x /≈) → (by : B y /≈)
        → QuotHetRel∀ B R bx by → QuotHetRel∃ B R bx by
QuotHetRel∀→∃ B R {x} {y} bx by = Bx.elimp P f bx by
  where
  module Bx = SetoidQuotient (B x)
  module By = SetoidQuotient (B y)

  P : B x /≈ → Prop _
  P bx = ∀ by → QuotHetRel∀ B R bx by → QuotHetRel∃ B R bx by

  f : ∀ bx₀ → P (Bx.[ bx₀ ])
  f bx₀ by p = By.elimp Q g by p
    where
    Q : B y /≈ → Prop _
    Q by = QuotHetRel∀ B R (Bx.[ bx₀ ]) by → QuotHetRel∃ B R (Bx.[ bx₀ ]) by

    g : ∀ by₀ → Q (By.[ by₀ ])
    g by₀ p = ∣ qrwitness bx₀ by₀ (p bx₀ by₀ ≡.refl ≡.refl) ≡.refl ≡.refl ∣

QuotHomRel∀ : ∀ {ℓB ℓB≈ ℓR} (B : Setoid ℓB ℓB≈)
        → (R : ⟨ B ⟩ → ⟨ B ⟩ → Prop ℓR)
        → (B /≈ → B /≈ → Prop (ℓB ⊔ ℓB≈ ⊔ ℓR))
QuotHomRel∀ B R b1 b2 =
    ∀ b1₀ b2₀ → (B ⊢[ b1₀ ] ≡ b1) → (B ⊢[ b2₀ ] ≡ b2) → R b1₀ b2₀

QuotHomRel∃ : ∀ {ℓB ℓB≈ ℓR} (B : Setoid ℓB ℓB≈)
        → (R : ⟨ B ⟩ → ⟨ B ⟩ → Prop ℓR)
        → (B /≈ → B /≈ → Prop (ℓB ⊔ ℓB≈ ⊔ ℓR))
QuotHomRel∃ B R x y = ∥ QuotRelWitness B B R x y ∥

QuotHomRel∀→∃ : ∀ {ℓB ℓB≈ ℓR} (B : Setoid ℓB ℓB≈)
        → (R : ⟨ B ⟩ → ⟨ B ⟩ → Prop ℓR)
        → (x y : B /≈)
        → QuotHomRel∀ B R x y → QuotHomRel∃ B R x y
QuotHomRel∀→∃ B R x y = elimp P f x y
  where
  open SetoidQuotient B
  P : B /≈ → Prop _
  P x = ∀ y → QuotHomRel∀ B R x y → QuotHomRel∃ B R x y

  f : ∀ x₀ → P [ x₀ ]
  f x₀ y p = elimp Q g y p
    where
    Q : B /≈ → Prop _
    Q y = QuotHomRel∀ B R [ x₀ ] y → QuotHomRel∃ B R [ x₀ ] y

    g : ∀ y₀ → Q [ y₀ ]
    g y₀ p = ∣ qrwitness x₀ y₀ (p x₀ y₀ ≡.refl ≡.refl) ≡.refl ≡.refl ∣
