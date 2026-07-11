module QIT.Prelude.Axiom where

open import QIT.Prelude.Universe
open import QIT.Prelude.Logic
open import QIT.Prelude.Identity
open import QIT.Prelude.HLevel

record PropExt : Propω where
  field
    propExt : ∀ {ℓA}
            → {A B : Prop ℓA}
            → A ⇔ B → A ≡ B

record A!C : Setω where
  field
    a!c : ∀ {ℓA} (A : Set ℓA) → isContr A → A

record FunExt : Propω where
  field
    funExt : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB}
           → {f g : ∀ a → B a} → (∀ x → f x ≡ g x)
           → f ≡ g

    funExtp : ∀ {ℓA ℓB} {A : Prop ℓA} {B : A → Set ℓB}
           → {f g : ∀ a → B a} → (∀ x → f x ≡ g x)
           → f ≡ g

-- P∧Q→P≡Q : ∀ {ℓP} {P Q : Prop ℓP} → P ∧ Q → P ≡ Q
-- P∧Q→P≡Q (p , q) = propExt ((λ _ → q) , (λ _ → p))

record PathElim : Setω where
  field
    J : {A : Set ℓA} {x : A}
      → (B : (y : A) → x ≡ y → Set ℓB)
      → {y : A} (p : x ≡ y) → B x refl → B y p
    J-refl : {A : Set ℓA} {x : A}
           → (B : (y : A) → x ≡ y → Set ℓB)
           → (Brefl : B x refl)
           → J B refl Brefl ≡ Brefl
