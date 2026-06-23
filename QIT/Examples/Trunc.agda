open import QIT.Prelude

-- An example of propositional truncation
-- Note that we don't get elimination to prop, so this isn't full
-- truncation.
module QIT.Examples.Trunc ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Container.Base
open import QIT.QW

sig : (A : Set) → QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
sig A = record
  { S = A
  ; P = λ _ → ⊥ˢ
  ; E = ⊤ˢ
  ; Ξ = λ _ → record
    { V = ⊤ˢ ⊎ ⊤ˢ
    ; lhs = QW.varᴱ (inj₁ tt) {λ()}
    ; rhs = QW.varᴱ (inj₂ tt) {λ()} } }
