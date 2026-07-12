open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient

module QIT.Examples.Mobile.Cocontinuity
  ⦃ propExt : PropExt ⦄
  ⦃ pathElim* : PathElim ⦄
  ⦃ sq* : SetQuotients ⦄
  ⦃ a!c : A!C ⦄
  ⦃ fe* : FunExt ⦄
  ⦃ epo* : ExtensionalPlumpOrdinals ⦄
  (I : Set)
  where

open import QIT.Examples.Mobile.Base I

open Sig sig

open import QIT.Plump.W S P
open import QIT.Plump.Properties Zᴬ as Z
open import QIT.QW.Subclasses sig

instance
  depthPreserving* : DepthPreservingSig
  depthPreserving* = record { dpe = dpe }
    where
    dpe : ∀ π ρ → ιᶻ (assignT ρ (Ξ π .lhs)) ≤≥ ιᶻ (assignT ρ (Ξ π .rhs))
    dpe π ρ = ∧i lhs≤rhs , rhs≤lhs
      where
      lhs≤rhs : ιᶻ (assignT ρ (Ξ π .lhs)) ≤ ιᶻ (assignT ρ (Ξ π .rhs))
      lhs≤rhs = sup≤ witness
        where
        step : ∀ i → ιᶻ (ρ i) ≡ ιᶻ (ρ (π .≅ˢ.to (π .≅ˢ.from i)))
        step i = ≡.sym (≡.cong (λ j → ιᶻ (ρ j)) (π .≅ˢ.linv i))

        witness : ∀ i → ιᶻ (ρ i) < ιᶻ (assignT ρ (Ξ π .rhs))
        witness i = <sup (π .≅ˢ.from i) (Z.≡→≤ (step i))

      rhs≤lhs : ιᶻ (assignT ρ (Ξ π .rhs)) ≤ ιᶻ (assignT ρ (Ξ π .lhs))
      rhs≤lhs = sup≤ λ i → <sup (π .≅ˢ.to i) (≤refl (ιᶻ (ρ (π .≅ˢ.to i))))

open import QIT.QW.Cocontinuity.FromDepthPreservation sig

ψ = Cocontinuity.ψ
ϕ = Cocontinuity.ϕ
ψϕ = Cocontinuity.ψϕ
ϕψ = Cocontinuity.ϕψ
cocontinuity = Cocontinuity.cocontinuity
