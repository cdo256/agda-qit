open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
import QIT.Container.Base as W

module QIT.Plump.Extensional.Properties {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

import QIT.Plump.W.Base S P as PlumpW
import QIT.Plump.Properties S P as Plump

open PlumpW public
  using (Sᶻ ; Pᶻ ; ιˢ ; ∨ˢ ; ⊥ˢ)
  renaming ( Z to Z₀; _≤_ to _≤₀_; _<_ to _<₀_; _≤≥_ to _≤≥₀_
           ; ≤≤ to ≤≤₀ ; ≤< to ≤<₀ ; <≤ to <≤₀
           ; sup≤ to sup≤₀ ; <sup to <sup₀)

open import QIT.Plump.Algebra Sᶻ Pᶻ public

module AlgProperties {ℓA}
  (ZA : Algebra ℓA)
  where
  open Plump.AlgProperties ZA public

  [_] : Z₀ → Z
  [ W.sup (s , ξ) ] = sup (s , λ i → [ ξ i ])

  <[_] : ∀ {α β} → α <₀ β → [ α ] < [ β ]
  ≤[_] : ∀ {α β} → α ≤₀ β → [ α ] ≤ [ β ]

  <[_] {α} {W.sup (s , ξ)} (<sup₀ i α≤ξi) = <sup i ≤[ α≤ξi ]
  ≤[_] {W.sup (s , ξ)} {β} (sup≤₀ ξ<α) = sup≤ (λ i → <[ ξ<α i ])
