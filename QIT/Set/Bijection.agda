open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Category.Base
open import QIT.Category.Set

module QIT.Set.Bijection ⦃ pathElim* : PathElim ⦄ where

module _ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} where

  IsInjection : (f : A → B) → Prop (ℓA ⊔ ℓB)
  IsInjection f = ∀ {x y} → f x ≡ f y → x ≡ y

  IsSurjection : (f : A → B) → Prop (ℓA ⊔ ℓB)
  IsSurjection f = ∀ y → ∃ λ x → f x ≡ y

  IsBijection : (f : A → B) → Prop (ℓA ⊔ ℓB)
  IsBijection f = IsInjection f ∧ IsSurjection f

module _ {ℓA ℓP ℓB} {A : Set ℓA} {P : A → Prop ℓP} {Q : A → Prop ℓP} {B : Set ℓB} where
  injΣP-restrict
    : (P⊆Q : ∀ {x} → P x → Q x) (f : ΣP A Q → B) (f-inj : IsInjection f)
    → IsInjection {A = ΣP A P} {B = B} (λ (x , p) → f (x , P⊆Q p))
  injΣP-restrict P⊆Q f f-inj {x , px} {y , py} r =
    ΣP≡ (x , px) (y , py) (≡.cong fst (f-inj r))

module _ {ℓX} {A B : Set ℓX} (ac : A!C) where
  open A!C ac

  open import QIT.Category.Morphism (SetCat ℓX)

  open Category (SetCat ℓX)

  Bijection→Iso : (f : A → B) → IsBijection f → Iso A B
  Bijection→Iso f (inj , surj) = iso
    where
    T : B → Set _
    T y = ΣP A (λ x → f x ≡ y)

    f⁻¹T : ∀ y → T y
    f⁻¹T y = a!c (T y) (isContrT (surj y))
      where
      isContrT : (∃ λ x → f x ≡ y) → isContr (T y)
      isContrT (∃.∃i x ≡.refl) = ∃.∃i (x , ≡.refl) (λ (x' , fx'≡fx) → ΣP≡ (x , _) (x' , _) (inj (≡.sym fx'≡fx)))

    f⁻¹ : B → A
    f⁻¹ y = fst (f⁻¹T y)

    iso : Iso A B
    iso = record
      { f    = f
      ; f⁻¹  = f⁻¹
      ; linv = λ {x} → inj (snd (f⁻¹T (f x)))
      ; rinv = λ {y} → (snd (f⁻¹T y)) }


module _ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} (ac : A!C) where
  open import QIT.Category.Morphism (SetCat (ℓA ⊔ ℓB))

  open Category (SetCat (ℓA ⊔ ℓB))

  HetBijection→Iso : (f : A → B) → IsBijection f → Lift ℓB A ≅ Lift ℓA B
  HetBijection→Iso f (inj , surj) = ∣ Bijection→Iso ac f' (inj' , surj') ∣
    where
    f' : Lift ℓB A → Lift ℓA B
    f' (lift x) = lift (f x)
    inj' : IsInjection f'
    inj' {lift x} {lift y} p = ≡.cong lift (inj (≡.cong lower p))
    surj' : IsSurjection f'
    surj' (lift y) with surj y
    ... | ∃.∃i x p = ∃.∃i (lift x) (≡.cong lift p)

↔to-Injection : ∀ {ℓX ℓY} {X : Set ℓX} {Y : Set ℓY}
              → (p : X ↔ Y) → IsInjection (p .↔.to)
↔to-Injection {ℓX} {ℓY} {X} {Y} p {x} {y} q =
  ≡.trans (≡.sym (p .↔.rinv x)) (≡.trans (≡.cong (p .↔.from) q) (p .↔.rinv y))
