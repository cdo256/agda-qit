open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Set.Base
open import QIT.Relation.SetQuotient
import QIT.SimpleDiagram

module QIT.Colimit
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ fe* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓI} {ℓ<}
  {I : Set ℓI}
  (<p : WeakPreorder I ℓ<)
  (ℓD : Level)
  (P : QIT.SimpleDiagram.Diagram {ℓA = ℓI} {ℓ< = ℓ<} {A = I} <p ℓD)
  where

open import QIT.Colimit.Properties <p ℓD P public
