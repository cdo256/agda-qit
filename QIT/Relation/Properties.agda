open import QIT.Prelude

module QIT.Relation.Properties ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Relation.Binary
open import QIT.Bool
open import QIT.Function.Base

module _ {ℓA ℓ<} (A : Set ℓA) (_<_ : A → A → Prop ℓ<) where
  Acc-irrefl : ∀ {α} → Acc _<_ α → ¬ (α < α)
  Acc-irrefl (acc rs) α<α =
    Acc-irrefl (rs _ α<α) α<α
