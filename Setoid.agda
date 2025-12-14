module Setoid where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.Bundles
open import Function.Bundles
open import Function.Definitions
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Relation.Binary.Definitions
open import Data.Product.Function.Dependent.Setoid 

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

open Setoid
open import Function.Relation.Binary.Setoid.Equality using () renaming (_≈_ to _≈⃗_)
open import Data.List.Relation.Binary.Equality.Setoid 
open import Relation.Binary.Morphism.Bundles 

private
  SetoidIso : ∀ ℓ ℓ' → Setoid ℓ ℓ' → Setoid ℓ ℓ' → Set  (ℓ ⊔ ℓ')
  SetoidIso ℓ ℓ' = SetoidIsomorphism {ℓ₁ = ℓ} {ℓ₂ = ℓ'} {ℓ₃ = ℓ} {ℓ₄ = ℓ'} 

module _ {ℓ ℓ'} where
  isEquivalenceSetoidIso : IsEquivalence (SetoidIso ℓ ℓ')
  isEquivalenceSetoidIso = record
    { refl = isReflexive
    ; sym = isSymmetric
    ; trans = isTransitive
    }
    where
    isReflexive : Reflexive (SetoidIso ℓ ℓ')
    isReflexive {x = A} = record
      { ⟦_⟧ = λ x → x
      ; isRelIsomorphism = record
        { isMonomorphism = record
          { isHomomorphism = record
            { cong = λ p → p }
          ; injective = λ p → p }
        ; surjective = λ p → p , λ q → q } }
    isSymmetric : Symmetric (SetoidIso ℓ ℓ')
    isSymmetric {x = A} {y = B} A≅B = record
      { ⟦_⟧ = ⟦_⟧
      ; isRelIsomorphism = record
        { isMonomorphism = record
          { isHomomorphism = record
            { cong = cong }
          ; injective = λ p → inv-injective p }
        ; surjective = λ p → ~.⟦ p ⟧
                     , λ q → ~.injective (B.trans (right-inv _) q) } }
      where
        module ~ = SetoidIsomorphism A≅B
        module A = Setoid A
        module B = Setoid B
        ⟦_⟧ : (y : B.Carrier) → A.Carrier
        ⟦ y ⟧ = ~.surjective y .proj₁
        right-inv : ∀ y → ~.⟦ ⟦ y ⟧ ⟧ B.≈ y
        right-inv y = ~.surjective y .proj₂ A.refl 

        cong : Congruent B._≈_ A._≈_ ⟦_⟧
        cong {x} {y} x≈y = ~.injective (begin
          ~.⟦ ⟦ x ⟧ ⟧  ≈⟨ right-inv x ⟩
          x            ≈⟨ x≈y ⟩
          y            ≈⟨ B.sym (right-inv y) ⟩
          ~.⟦ ⟦ y ⟧ ⟧  ∎)
          where
          open import Relation.Binary.Reasoning.Setoid B

        inv-injective : Injective B._≈_ A._≈_ ⟦_⟧
        inv-injective {x} {y} gx≈gy = begin
          x            ≈⟨ B.sym (right-inv x) ⟩
          ~.⟦ ⟦ x ⟧ ⟧  ≈⟨ ~.cong gx≈gy ⟩
          ~.⟦ ⟦ y ⟧ ⟧  ≈⟨ right-inv y ⟩
          y            ∎
          where
          open import Relation.Binary.Reasoning.Setoid B

        inv-surjective : Surjective B._≈_ A._≈_ ⟦_⟧
        inv-surjective x = ~.⟦ x ⟧ , v
          where
          v : ∀ {z} → z B.≈ ~.⟦ x ⟧ → ⟦ z ⟧ A.≈ x
          v {z} z≈⟦x⟧ = ~.injective
                        (B.trans (~.surjective z .proj₂ A.refl) z≈⟦x⟧)
    isTransitive : Transitive (SetoidIso ℓ ℓ')
    isTransitive {i = A} {j = B} {k = C} p q = record
      { ⟦_⟧ = λ x → q.⟦ p.⟦ x ⟧ ⟧
      ; isRelIsomorphism = record
        { isMonomorphism = record
          { isHomomorphism = record
            { cong = λ r → q.cong (p.cong r) }
          ; injective = λ r → p.injective (q.injective r) }
        ; surjective = λ r → p.surjective (q.surjective r .proj₁) .proj₁
                     , λ s → q.surjective r .proj₂
                              (p.surjective (q.surjective r .proj₁) .proj₂ s) } }
      where
        module p = SetoidIsomorphism p
        module q = SetoidIsomorphism q
        module A = Setoid A
        module B = Setoid B
        module C = Setoid C

  SetoidSetoid : Setoid (lsuc ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  SetoidSetoid = record
    { Carrier = Setoid ℓ ℓ'
    ; _≈_ = SetoidIso ℓ ℓ'
    ; isEquivalence = isEquivalenceSetoidIso
    }

infixr 1 _∘_
_∘_ : ∀ {c₁ c₂ c₃ ℓ₁ ℓ₂ ℓ₃}
        {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂} {C : Setoid c₃ ℓ₃} →
        Func B C → Func A B → Func A C
f ∘ g = record
  { to   = λ x → f .Func.to (g .Func.to x)
  ; cong = λ x≈y → f .Func.cong (g .Func.cong x≈y)
  }
