open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Category.Base
open import QIT.Category.Set


module QIT.Set.Bijection where

module _ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} where
  open import QIT.Category.Morphism (SetCat (ℓA ⊔ ℓB))

  open Category (SetCat (ℓA ⊔ ℓB))

  IsInjection : (f : A → B) → Prop (ℓA ⊔ ℓB)
  IsInjection f = ∀ {x y} → f x ≡ f y → x ≡ y

  IsSurjection : (f : A → B) → Prop (ℓA ⊔ ℓB)
  IsSurjection f = ∀ y → ∃ λ x → f x ≡ y

  IsBijection : (f : A → B) → Prop (ℓA ⊔ ℓB)
  IsBijection f = IsInjection f ∧ IsSurjection f

  postulate
    A!C : ∀ {ℓX} (X : Set ℓX) → isContr X → X

  Bijection→Iso : (f : A → B) → IsBijection f → Lift ℓB A ≅ Lift ℓA B
  Bijection→Iso f (inj , surj) = ∣ iso ∣
    where
    T : B → Set _
    T y = ΣP A (λ x → f x ≡ y)

    f⁻¹T : ∀ y → T y
    f⁻¹T y = A!C (T y) (isContrT (surj y))
      where
      isContrT : (∃ λ x → f x ≡ y) → isContr (T y)
      isContrT ∣ x , ≡.refl ∣ = ∣ (x , ≡.refl) , (λ (x' , fx'≡fx) → ΣP≡ (x , _) (x' , _) (inj (≡.sym fx'≡fx))) ∣

    f⁻¹ : B → A
    f⁻¹ y = fst (f⁻¹T y)

    iso : Iso (Lift ℓB A) (Lift ℓA B)
    iso = record
      { f    = λ (lift x) → lift (f x)
      ; f⁻¹  = λ (lift y) → lift (f⁻¹ y)
      ; linv = ≡.funExt λ (lift x) → ≡.cong lift (inj (snd (f⁻¹T (f x))))
      ; rinv = ≡.funExt λ (lift y) → ≡.cong lift (snd (f⁻¹T y)) }
