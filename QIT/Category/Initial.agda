open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Set.Base
open import QIT.Setoid
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Category.Base
open import QIT.Category.SetoidEnriched

module QIT.Category.Initial where
private
  variable
    ℓCo ℓCh ℓCe : Level

module _ (C : Category ℓCo ℓCh ℓCe) where
  open Category C

  isWeaklyInitial : (x : Obj) → Set (ℓCo ⊔ ℓCh)
  isWeaklyInitial x = ∀ (y : Obj) → x ⇒ y

  isInitial : (x : Obj) → Set (ℓCo ⊔ ℓCh)
  isInitial x = ∀ y → isProp (x ⇒ y)
