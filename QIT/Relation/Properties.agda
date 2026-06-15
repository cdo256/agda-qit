module QIT.Relation.Properties where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
import Data.Bool as Bool
open Bool using (Bool; true; false)

open import QIT.Function.Base

A!C-Prop : ∀ {ℓX} (X : Set ℓX)
          → isProp X → (Box ∥ X ∥) ↔ X
A!C-Prop X isPropX = record
  { to = λ (box x) → A!C X (mkIsContr X x isPropX)
  ; from = λ z → box ∣ z ∣
  ; rinv = λ _ → ≡.isPropBox _ _
  ; linv = λ _ → isPropX _ _ }

Prop≅hProp-sect
  : ∀ {ℓA} → (A : hProp ℓA)
  → Prop→hProp (hProp→Prop A) .fst ↔ A .fst
Prop≅hProp-sect (A , isPropA) = A!C-Prop A isPropA
