open import QIT.QW.Cocontinuity.FromDepthPreservation.Prelude

module QIT.QW.Cocontinuity.FromDepthPreservation.Rank
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

open import QIT.QW.Cocontinuity.FromDepthPreservation.DepthPreserving sig ℓA

open import QIT.QW.Subclasses sig hiding (DepthPreservingSig)

open Sig sig
open A!C a!c*
open FunExt funExt*
open ExtensionalPlumpOrdinals extensionalPlumpOrdinals*

open import QIT.QW.StageColimit sig Zᴬ

open import QIT.Plump.Properties Zᴬ

open import QIT.QW.Algebra sig
-- open import QIT.QW.Colimit ≤p ℓD ℓD' hiding (_≈ˡ_)

private
  ℓc = ℓA ⊔ ℓS ⊔ ℓP
  ℓc' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

open import QIT.Container.Base
open import QIT.Functor.Properties renaming (_∘_ to _∘ꟳ_)
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))
open import QIT.Setoid.Quotient
open import QIT.QW.Equation
open import QIT.QW.Colimit.Base ≤p ℓc ℓc'
open import QIT.Container.Properties 

Cocontinuous : (F : Functor (SetCat (ℓc ⊔ ℓc')) (SetCat (ℓc ⊔ ℓc'))) (D : Diagram/≈ ℓc ℓc')
              → Prop ℓc'
Cocontinuous F D =
  Colim/≈ (F ∘ꟳ D) ≅ Functor.ob F (Colim/≈ D)

module ColimF∘D = SQ (Colim (F ∘ D))
module ColimD = SQ (Colim D)
module Ob = Functor F
open SQ

rankD₀ : ∀ {α} → D₀ α → Z
rankD₀ (t , _) = ιᶻ t

rankD-cong : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → rankD₀ ŝ ≡ rankD₀ t̂
rankD-cong {α} {ŝ} {t̂} p = dp α ŝ t̂ p

rankD : ∀ {α} → D̃ α /≈ → Z
rankD {α} = rec (D̃ α) rankD₀ rankD-cong

rankD-beta : ∀ {α} (t̂ : D₀ α) → rankD (D̃ α ⊢[ t̂ ]) ≡ rankD₀ t̂
rankD-beta {α} t̂ = rec-beta (D̃ α) rankD₀ rankD-cong t̂

hom-beta : ∀ {α β} (p : α ≤ β) (t̂ : D₀ α)
          → D/≈.hom (box p) (D̃ α ⊢[ t̂ ]) ≡ D̃ β ⊢[ pweaken p t̂ ]
hom-beta {α} {β} p t̂ =
  rec-beta (D̃ α)
    (λ x → D̃ β ⊢[ pweaken p x ])
    (λ {x y} q → D̃ β ⊢≈[ ≈pweaken p q ])
    t̂

rankD-step : ∀ {α β} (p : α ≤ β) (t̂ : D₀ α)
                → rankD (D̃ α ⊢[ t̂ ]) ≡ rankD (D/≈.hom (box p) (D̃ α ⊢[ t̂ ]))
rankD-step p t̂ =
  ≡.trans (rankD-beta t̂)
    (≡.trans ≡.refl
      (≡.trans (≡.sym (rankD-beta (pweaken p t̂)))
        (≡.cong rankD (≡.sym (hom-beta p t̂)))))

rankC : Colim/≈ D → Z
rankC = rec (Colim D) (λ (_ , t̂) → rankD t̂) stable
  where
  stable : ∀ {x y} → Colim D [ x ≈ y ] → rankD (x .proj₂) ≡ rankD (y .proj₂)
  stable (≈lstage i p) = ≡.cong rankD p
  stable (≈lstep {α} {β} p x) =
    elimp (D̃ α)
          (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
          (rankD-step p)
          x
  stable (≈lsym p) = ≡.sym (stable p)
  stable (≈ltrans p q) = ≡.trans (stable p) (stable q)
