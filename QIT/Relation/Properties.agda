module QIT.Relation.Properties where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Relation.Binary
import Data.Bool as Bool
open Bool using (Bool; true; false)

open import QIT.Function.Base

module _ (a!c : A!C) where
  a!c-Prop : ∀ {ℓX} (X : Set ℓX)
            → isProp X → (Box ∥ X ∥) ↔ X
  a!c-Prop X isPropX = record
    { to = λ (box x) → a!c X (mkIsContr X x isPropX)
    ; from = λ z → box ∣ z ∣
    ; rinv = λ _ → ≡.isPropBox _ _
    ; linv = λ _ → isPropX _ _ }

  Prop≅hProp-sect
    : ∀ {ℓA} → (A : hProp ℓA)
    → Prop→hProp (hProp→Prop A) .fst ↔ A .fst
  Prop≅hProp-sect (A , isPropA) = a!c-Prop A isPropA

module _ {ℓA ℓ<} (A : Set ℓA) (_<_ : A → A → Prop ℓ<) where
  Acc-irrefl : ∀ {α} → Acc _<_ α → ¬ (α < α)
  Acc-irrefl (acc rs) α<α =
    Acc-irrefl (rs _ α<α) α<α
