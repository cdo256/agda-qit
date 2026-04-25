module QIT.Category.Equivalence where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Setoid.Base 
open import QIT.Relation.Binary
open import QIT.Relation.Base
open import QIT.Category.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Functor.NatTrans

record Equivalence {ℓCo ℓCh ℓCe ℓDo ℓDh ℓDe}
  (C : Category ℓCo ℓCh ℓCe) (D : Category ℓDo ℓDh ℓDe)
  : Set (ℓCo ⊔ ℓCh ⊔ ℓCe ⊔ ℓDo ⊔ ℓDh ⊔ ℓDe) where
  module C = Category C
  module D = Category D
  field
    F : Functor C D
    G : Functor D C
    η : NatIso Id (G ∘ F)
    ε : NatIso (F ∘ G) Id
