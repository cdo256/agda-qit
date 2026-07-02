open import QIT.Prelude
open import QIT.Logic
open import QIT.QW.Signature
open import QIT.Plump.Algebra
import QIT.Plump.Properties

module QIT.QW.Plump
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

record ExtensionalPlumpOrdinals ℓA
  : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ lsuc ℓA)
  where
  open Sig sig
  field
    Zᴬ : PlumpAlgebra S P ℓA ℓA ℓA

  open QIT.Plump.Properties Zᴬ

  field
    isExtensionalZᴬ : IsExtensional

  open IsExtensional isExtensionalZᴬ public
  import QIT.Plump.W S P as Z₀
  import QIT.Container.Base as W
  [_]ᶻ : Z₀.Z → Z
  [ W.sup (Z₀.⊥ₛ , f) ]ᶻ = ⊥ᶻ
  [ W.sup (Z₀.∨ₛ , f) ]ᶻ =
       [ f (inj₁ tt*) ]ᶻ
    ∨ᶻ [ f (inj₂ tt*) ]ᶻ
  [ W.sup (Z₀.ιₛ s , f) ]ᶻ =
    sup (s , λ i → [ f i ]ᶻ)
  ≤[_]ᶻ : ∀ {α β : Z₀.Z}
        → α Z₀.≤ β → [ α ]ᶻ ≤ [ β ]ᶻ
  <[_]ᶻ : ∀ {α β : Z₀.Z}
        → α Z₀.< β → [ α ]ᶻ < [ β ]ᶻ
  <[_]ᶻ {α} {W.sup (Z₀.⊥ₛ , ξ)} (Z₀.<sup () α≤ξi)
  <[_]ᶻ {α} {W.sup (Z₀.∨ₛ , ξ)} (Z₀.<sup (inj₁ tt*) α≤ξ₁) =
    <≤ ∨ᶻ-l< ≤[ α≤ξ₁ ]ᶻ
  <[_]ᶻ {α} {W.sup (Z₀.∨ₛ , ξ)} (Z₀.<sup (inj₂ tt*) α≤ξ₂) =
    <≤ ∨ᶻ-r< ≤[ α≤ξ₂ ]ᶻ
  <[_]ᶻ {α} {W.sup (Z₀.ιₛ s , ξ)} (Z₀.<sup i α≤ξi) =
    <sup i ≤[ α≤ξi ]ᶻ
  ≤[_]ᶻ {W.sup (Z₀.⊥ₛ , ξ)} {β} _ = ⊥ᶻ≤
  ≤[_]ᶻ {W.sup (Z₀.∨ₛ , ξ)} {β} (Z₀.sup≤ ξ<β) =
    ∨ᶻ≤ <[ ξ<β (inj₁ tt*) ]ᶻ <[ ξ<β (inj₂ tt*) ]ᶻ
  ≤[_]ᶻ {W.sup (Z₀.ιₛ s , ξ)} {β} (Z₀.sup≤ ξ<β) =
    sup≤ (λ i → <[ ξ<β i ]ᶻ)
