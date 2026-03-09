module QIT.Category.Morphism where

open import QIT.Prelude
open import QIT.Category.Base

module _ {ℓCo} {ℓCh} {ℓCe} (C : Category ℓCo ℓCh ℓCe) where
  private
    module C = Category C
  record IsIso {x y} (f : C [ x , y ]) : Set (ℓCh ⊔ ℓCe) where
    field
      g : C [ y , x ]
      linv : g C.∘ f C.≈ C.id
      rinv : f C.∘ g C.≈ C.id
