open import QIT.Prelude
open import QIT.Relation.SetQuotient

module QIT.Setoid.IndexedQuotient
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  where

open import QIT.Relation.Base
open import QIT.Relation.IndexedBinary
open import QIT.Setoid.Indexed as IS
open import QIT.Setoid.Base as S
open import QIT.Setoid.Quotient as Q

_/≈ᴵ : IS.Setoid ℓI ℓA ℓR → Set (ℓI ⊔ ℓA ⊔ ℓR)
S /≈ᴵ = IndexedSetoid→UnindexedSetoid S Q./≈
