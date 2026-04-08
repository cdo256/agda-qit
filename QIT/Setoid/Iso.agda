open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
open import QIT.Category.Setoid

-- Define isomorphisms between setoids: bijective homomorphisms with
-- inverse operations. An isomorphism witnesses that two setoids are
-- "essentially the same" - they have the same structure up to renaming.
module QIT.Setoid.Iso {ℓA ℓA≈} where

open import QIT.Category.Morphism (SetoidCat ℓA ℓA≈)

-- The setoid of setoids: setoids form a setoid under isomorphism
SetoidSetoid : Setoid (lsuc ℓA ⊔ lsuc ℓA≈) (ℓA ⊔ ℓA≈)
SetoidSetoid = IsoSetoid
