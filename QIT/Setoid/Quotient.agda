open import QIT.Prelude
open import QIT.Identity as ≡ hiding (refl; sym; trans; cong)
open import QIT.Logic
open import QIT.Setoid.Base
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Relation.SetQuotient

module QIT.Setoid.Quotient
  ⦃ pathElim* : PathElim ⦄
  ⦃ fe* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ sq* : SetQuotients ⦄
  where

open PropExt propExt*
open FunExt funExt*

_/≈ : ∀ {ℓA ℓR} (Ã : Setoid ℓA ℓR) → Set (ℓA ⊔ ℓR)
Ã /≈ = A / _≈_
  where
  open Setoid Ã renaming (Carrier to A)

module SQ {ℓA ℓR} (Ã : Setoid ℓA ℓR) where
  abstract
    open Setoid Ã renaming (Carrier to A)
    [_] : A → Ã /≈
    [_] = Q.[_]

    []-beta : ∀ x → [ x ] ≡ Q.[ x ]
    []-beta x = ≡.refl

    ≈[_] : ∀ {x y} → x ≈ y → [ x ] ≡ [ y ]
    ≈[_] p = Q.quot-rel _ _ p

    rec
      : ∀ {ℓB} {B : Set ℓB}
      → (f : A → B)
      → (eq : {x y : A} → x ≈ y → f x ≡ f y)
      → Ã /≈ → B
    rec f eq = Q.quot-rec f λ _ _ → eq

    rec₂
      : ∀ {ℓB} {B : Set ℓB}
      → (f : A → A → B)
      → (eq : {x y z w : A} → x ≈ y → z ≈ w → f x z ≡ f y w)
      → Ã /≈ → Ã /≈ → B
    rec₂ {B = B} f eq = rec g g-cong
      where
      g : A → Ã /≈ → B
      g x = rec (f x) (eq {x = x} {y = x} (Setoid.refl Ã))
      g-cong : ∀ {x y} → x ≈ y → g x ≡ g y
      g-cong {x} {y} p =
        funExt (Q.quot-elimp
          (λ z → rec (f x) (eq {x = x} {y = x} (Setoid.refl Ã)) z ≡ rec (f y) (eq {x = y} {y = y} (Setoid.refl Ã)) z)
          (λ a →
            ≡.trans (Q.quot-rec-beta (f x) (λ _ _ → eq {x = x} {y = x} (Setoid.refl Ã)) a)
              (≡.trans (eq p (Setoid.refl Ã))
                (≡.sym (Q.quot-rec-beta (f y) (λ _ _ → eq {x = y} {y = y} (Setoid.refl Ã)) a)))))

    elim
      : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
      → (f : ∀ a → B [ a ])
      → (eq : {x y : A} → (r : x ≈ y) → subst B ≈[ r ] (f x) ≡ (f y))
      → ∀ a/ → B a/
    elim B f eq = Q.quot-elim B f λ _ _ → eq

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
      x≈a⇔x≈b : ∀ {a b} (a≈b : a ≈ b) → x ≈ a ⇔ x ≈ b
      x≈a⇔x≈b a≈b .∧e₁ x≈a = trans x≈a a≈b
      x≈a⇔x≈b a≈b .∧e₂ x≈b = trans x≈b (sym a≈b)

      P : Ã /≈ → Set ℓR
      P = rec
            (λ a → Box (x ≈ a))
            (λ a≈b → ≡.cong Box (propExt (x≈a⇔x≈b a≈b)))

      βx : P [ x ] ≡ Box (x ≈ x)
      βx = Q.quot-rec-beta (λ a → Box (x ≈ a))
            (λ _ _ a≈b → ≡.cong Box (propExt (x≈a⇔x≈b a≈b))) x

      px : P [ x ]
      px = ≡.subst (λ X → X) (≡.sym βx) (box refl)

      βy : P [ y ] ≡ Box (x ≈ y)
      βy = Q.quot-rec-beta (λ a → Box (x ≈ a))
            (λ _ _ a≈b → ≡.cong Box (propExt (x≈a⇔x≈b a≈b))) y

      py : Box (x ≈ y)
      py = ≡.subst (λ X → X) βy (≡.subst P p px)

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
    rec-beta f eq x = Q.quot-rec-beta f (λ _ _ → eq) x

    rec₂-beta
      : ∀ {ℓB} {B : Set ℓB}
      → (f : A → A → B)
      → (eq : {x y z w : A} → x ≈ y → z ≈ w → f x z ≡ f y w) (x z : A)
      → rec₂ f eq [ x ] [ z ] ≡ f x z
    rec₂-beta {B = B} f eq x z =
      ≡.trans
        (≡.cong (λ h → h [ z ]) (rec-beta g g-cong x))
        (rec-beta (f x) (eq {x = x} {y = x} (Setoid.refl Ã)) z)
      where
      g : A → Ã /≈ → B
      g x = rec (f x) (eq {x = x} {y = x} (Setoid.refl Ã))

      g-cong : {x y : A} → x ≈ y → g x ≡ g y
      g-cong {x} {y} p =
        funExt (Q.quot-elimp
          (λ q → rec (f x) (eq {x = x} {y = x} (Setoid.refl Ã)) q ≡ rec (f y) (eq {x = y} {y = y} (Setoid.refl Ã)) q)
          (λ a →
            ≡.trans (Q.quot-rec-beta (f x) (λ _ _ → eq {x = x} {y = x} (Setoid.refl Ã)) a)
              (≡.trans (eq p (Setoid.refl Ã))
                (≡.sym (Q.quot-rec-beta (f y) (λ _ _ → eq {x = y} {y = y} (Setoid.refl Ã)) a)))))

    elim-beta
      : ∀ {ℓB} (B : Ã /≈ → Set ℓB)
      → (f : ∀ a → B [ a ])
      → (eq : {x y : A} → (r : x ≈ y) → subst B ≈[ r ] (f x) ≡ (f y))
      → (x : A)
      → elim B f eq [ x ] ≡ f x
    elim-beta B f eq x = Q.quot-elim-beta B f (λ _ _ → eq) x

    elim₂
      : ∀ {ℓX} (X : Ã /≈ → Ã /≈ → Set ℓX)
      → (f : ∀ a b → X [ a ] [ b ])
      → (eq : ∀ {x y z w} (r : x ≈ y) (s : z ≈ w)
            → ≡.subst₂ X ≈[ r ] ≈[ s ] (f x z) ≡ f y w)
      → ∀ a/ b/ → X a/ b/
    elim₂ X f eq = elim (λ a/ → ∀ b/ → X a/ b/) p q
      where
      eq-right : ∀ a {x y} (r : x ≈ y)
               → ≡.subst (X [ a ]) ≈[ r ] (f a x) ≡ f a y
      eq-right a r =
        eq (Setoid.refl Ã) r

      p : (a : A) (b/ : Ã /≈) → X [ a ] b/
      p a = elim (X [ a ]) (f a) (eq-right a)
      q : {a a' : A} (a≈a' : a ≈ a')
        → ≡.subst (λ a/ → ∀ b/ → X a/ b/) ≈[ a≈a' ] (p a) ≡ p a' 
      q {a} {a'} a≈a' = funExt (elimp (λ b/ → _) r)
        where
        r : (b : A)
          → ≡.subst (λ a/ → ∀ b/ → X a/ b/) ≈[ a≈a' ] (p a) [ b ]
          ≡ p a' [ b ]
        r b = 
          ≡.subst (λ a/ → ∀ b/ → X a/ b/) ≈[ a≈a' ] (p a) [ b ]
            ≡⟨ ≡.subst-Π X ≈[ a≈a' ] (p a) [ b ] ⟩
          ≡.subst (λ a/ → X a/ [ b ]) ≈[ a≈a' ] (p a [ b ])
            ≡⟨ ≡.cong (≡.subst (λ a/ → X a/ [ b ]) ≈[ a≈a' ])
                      (elim-beta (X [ a ]) (f a) (eq-right a) b) ⟩
          ≡.subst (λ a/ → X a/ [ b ]) ≈[ a≈a' ]
                  (f a b)
            ≡⟨ eq {x = a} {y = a'} {z = b} {w = b} a≈a' (Setoid.refl Ã) ⟩
          f a' b
            ≡⟨ ≡.sym (elim-beta (X [ a' ]) (f a') (eq-right a') b) ⟩
          p a' [ b ] ∎
          where open ≡.≡-Reasoning


open SQ using () renaming ([_] to _⊢[_]; ≈[_] to _⊢≈[_]) public

map : ∀ {ℓA ℓR ℓB ℓS}
    → (Ã : Setoid ℓA ℓR)
    → (B̃ : Setoid ℓB ℓS)
    → (f₀ : ⟨ Ã ⟩ → ⟨ B̃ ⟩)
    → (f-cong : ∀ {x y : ⟨ Ã ⟩} → Ã [ x ≈ y ] → B̃ [ f₀ x ≈ f₀ y ])
    → Ã /≈ → B̃ /≈
map Ã B̃ f₀ f-cong =
  SQ.rec Ã (λ x → B̃ ⊢[ f₀ x ])
           (λ p → B̃ ⊢≈[ f-cong p ])
  where
  module B = Setoid B̃

map-beta
  : ∀ {ℓA ℓR ℓB ℓS}
  → (Ã : Setoid ℓA ℓR)
  → (B̃ : Setoid ℓB ℓS)
  → (f₀ : ⟨ Ã ⟩ → ⟨ B̃ ⟩)
  → (f-cong : ∀ {x y : ⟨ Ã ⟩} → Ã [ x ≈ y ] → B̃ [ f₀ x ≈ f₀ y ])
  → (a : ⟨ Ã ⟩)
  → map Ã B̃ f₀ f-cong (Ã ⊢[ a ]) ≡ B̃ ⊢[ f₀ a ]
map-beta Ã B̃ f₀ f-cong a =
      SQ.rec-beta Ã (λ x → B̃ ⊢[ f₀ x ])
                    (λ p → B̃ ⊢≈[ f-cong p ]) a
  where
  module B = Setoid B̃


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
  module Bx = SQ (B x)
  module By = SQ (B y)

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
  open SQ B
  P : B /≈ → Prop _
  P x = ∀ y → QuotHomRel∀ B R x y → QuotHomRel∃ B R x y

  f : ∀ x₀ → P [ x₀ ]
  f x₀ y p = elimp Q g y p
    where
    Q : B /≈ → Prop _
    Q y = QuotHomRel∀ B R [ x₀ ] y → QuotHomRel∃ B R [ x₀ ] y

    g : ∀ y₀ → Q [ y₀ ]
    g y₀ p = ∣ qrwitness x₀ y₀ (p x₀ y₀ ≡.refl ≡.refl) ≡.refl ≡.refl ∣
