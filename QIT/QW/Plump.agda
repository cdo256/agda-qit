open import QIT.Prelude
open import QIT.Logic
open import QIT.QW.Signature
open import QIT.Plump.Algebra
import QIT.Plump.Properties
open import QIT.Prop

module QIT.QW.Plump
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

open FunExt funExt*

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
  module Z₀Prop = QIT.Plump.Properties Z₀.Zᴬ
  import QIT.Container.Base as W
  [_]ᶻ : Z₀.Z → Z
  [ W.sup (Z₀.⊥ₛ , f) ]ᶻ = ⊥ᶻ
  [ W.sup (Z₀.∨ₛ , f) ]ᶻ =
       [ f (inj₁ tt*) ]ᶻ
    ∨ᶻ [ f (inj₂ tt*) ]ᶻ
  [ W.sup (Z₀.ιₛ s , f) ]ᶻ =
    sup (s , λ i → [ f i ]ᶻ)
  ιᶻ-factors : ∀ x → [ Z₀Prop.ιᶻ x ]ᶻ ≡ ιᶻ x
  ιᶻ-factors (W.sup (s , f)) =
    ≡.cong (λ ○ → sup (s , ○))
           (funExt λ i → ιᶻ-factors (f i))
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

  ιᶻ≤ιᶻ : ∀ x y
    → Z₀Prop.ιᶻ x Z₀.≤ Z₀Prop.ιᶻ y 
    → ιᶻ x ≤ ιᶻ y
  ιᶻ≤ιᶻ x y p =
    ≡.substp₂ _≤_
      (ιᶻ-factors x)
      (ιᶻ-factors y)
      ≤[ p ]ᶻ

  ιᶻ≤≥ιᶻ : ∀ x y
    → Z₀Prop.ιᶻ x Z₀.≤≥ Z₀Prop.ιᶻ y 
    → ιᶻ x ≤ ιᶻ y ∧ ιᶻ y ≤ ιᶻ x
  ιᶻ≤≥ιᶻ x y (∧i p , q) = ∧i ιᶻ≤ιᶻ x y p , ιᶻ≤ιᶻ y x q
