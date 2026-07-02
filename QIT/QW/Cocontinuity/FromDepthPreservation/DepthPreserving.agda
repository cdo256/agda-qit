open import QIT.QW.Cocontinuity.FromDepthPreservation.Prelude

module QIT.QW.Cocontinuity.FromDepthPreservation.DepthPreserving
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (ℓA : Level)
  ⦃ depthPreserving* : DepthPreservingSig sig ⦄
  ⦃ extensionalPlumpOrdinals* : ExtensionalPlumpOrdinals sig ℓA ⦄
  where

private
  ℓc = ℓA ⊔ ℓS ⊔ ℓP
  ℓc' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

open Sig sig
open FunExt funExt*
open ExtensionalPlumpOrdinals extensionalPlumpOrdinals*
open DepthPreservingSig depthPreserving* renaming (dp to dp-syntax)

open import QIT.QW.StageColimit sig Zᴬ
open import QIT.Plump.Properties Zᴬ
open import QIT.QW.Equation

module Eq = Equation
open import QIT.Nat

open import QIT.Plump.W S P as Z₀
open Z₀ renaming (Z to Z₀)

dp : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≡ ιᶻ (t̂ .fst)
dp α ŝ t̂ (≈pcong a μ f g r) =
  ≡.cong (λ ○ → Z.sup (a , ○))
        (funExt λ i → dp (μ i) (f i) (g i) (r i))
dp α (s , s≤α) (t , t≤α) (≈psat e ϕ _ _) =
  let ∧i p , q = ιᶻ≤≥ιᶻ (lhs' e ϕ) (rhs' e ϕ)
                        (dp-syntax e λ v → lower (ϕ v))
  in antisym p q
dp α ŝ t̂ ≈prefl = ≡.refl
dp α ŝ t̂ (≈psym p) = ≡.sym (dp _ _ _ p)
dp α ŝ t̂ (≈ptrans p q) = ≡.trans (dp _ _ _ p) (dp _ _ _ q)
dp β _ _ (≈pweaken {α} α≤β {ŝ} {t̂} p) = dp α ŝ t̂ p
