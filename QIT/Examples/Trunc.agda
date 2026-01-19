-- An example of propositional truncation
-- Note that we don't get elimination to prop, so this isn't full
-- truncation.
module QIT.Examples.Trunc where

open import QIT.Prelude
open import QIT.Container.Base
open import QIT.QW

sig : (A : Set) → QW.Sig ℓ0 ℓ0 ℓ0 ℓ0
sig A = record
  { S = A
  ; P = λ _ → ⊥
  ; E = ⊤
  ; Ξ = λ _ → record
    { V = ⊤ ⊎ ⊤
    ; lhs = QW.varᴱ (inj₁ tt) {λ()}
    ; rhs = QW.varᴱ (inj₂ tt) {λ()} } }
