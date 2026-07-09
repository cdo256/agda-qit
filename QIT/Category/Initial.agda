open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Setoid
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Category.Base

module QIT.Category.Initial
  ⦃ pathElim* : PathElim ⦄
  {ℓCo} {ℓCh} {ℓCe} (C : Category ℓCo ℓCh ℓCe) where

open Category C

isWeaklyInitial : (x : Obj) → Prop (ℓCo ⊔ ℓCh)
isWeaklyInitial x = ∀ (y : Obj) → ∥ x ⇒ y ∥

record isInitial (x : Obj) : Set (ℓCo ⊔ ℓCh ⊔ ℓCe) where
  field
    hom : ∀ y → x ⇒ y
    unique : ∀ y → (f : x ⇒ y) → hom y ≡ f

Initial : Set (ℓCo ⊔ ℓCh ⊔ ℓCe)
Initial = Σ Obj isInitial
