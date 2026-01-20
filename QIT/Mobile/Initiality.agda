{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.Mobile.Initiality
  (I : Set) (inhabI : ∥ I ∥) where

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Mobile.Base I
open import QIT.Mobile.Cocontinuity I inhabI
open import QIT.Setoid as ≈
open import QIT.Container.Base
open import QIT.Relation.Plump Sᵀ Pᵀ
open import QIT.Setoid.Diagram ≤p

open import QIT.QW.Colimit ≤p ℓ0 (lsuc ℓ0) hiding (_≈ˡ_)
open import QIT.QW.Cocontinuity ≤p
open import QIT.QW.Stage sig
open import QIT.QW.Algebra sig
open import QIT.QW.StageColimit sig using (joinTerms; αˡ; tˡ; t≤αˡ)
open import QIT.QW.Equation Sᵀ Pᵀ
open import QIT.QW.W sig hiding (T)

open import QIT.QW.Signature
open Sig sig

open import QIT.Container.Functor Sᵀ Pᵀ ℓ0 (lsuc ℓ0)

open F-Ob

θ₀ : ⟨ Colim (F ∘ᴰ D) ⟩ → ⟨ Colim D ⟩
θ₀ (α , a , f) = β , t , t≤β
  where
  β : Z
  β = sup (ιˢ a , λ _ → α)
  t : T
  t = sup (a , λ i → f i .fst)
  t≤β : t ≤ᵀ β
  t≤β = sup≤sup λ i → f i .snd

θ-cong : ∀ {x y} → Colim (F ∘ᴰ D) [ x ≈ y ] → Colim D [ θ₀ x ≈ θ₀ y ]
θ-cong {α , (a , f)} {α , (b , g)} (≈lstage α (mk≈ꟳ ≡.refl snd≈)) =
  ≈lstage (sup (ιˢ a , (λ _ → α))) (≈pcong a (λ _ → α) f g snd≈)
θ-cong {α , (a , f)} {β , (a , g)} (≈lstep p (a , f)) =
  ≈lstep (sup≤sup λ _ → p) (sup (a , (λ i → f i .fst)) , _)
θ-cong {α , (a , f)} {β , (b , g)} (≈lsym p) =
  ≈lsym (θ-cong p)
θ-cong {α , (a , f)} {β , (b , g)} (≈ltrans p q) =
  ≈ltrans (θ-cong p) (θ-cong q)

θ : ≈.Hom (Colim (F ∘ᴰ D)) (Colim D)
θ = record { to = θ₀ ; cong = θ-cong }

-- Main theorem: cocontinuous functors give initial algebras
theorem : Cocontinuous F D → ∥ Record ∥
theorem ∣ iso ∣ = ∣ record
  { Xα = record
    { alg = Xα
    ; sat = sat }
  ; initial = record
    { rec = {!!}
    ; unique = {!!} } } ∣
  where
  -- open ≈.Iso iso renaming (⟦_⟧ to ϕ₀; cong to ϕ-cong; ⟦_⟧⁻¹ to ψ₀; cong⁻¹ to ψ-cong)
  ϕ : ≈.Hom (Colim (F ∘ᴰ D)) (F.F-ob (Colim D))
  ϕ = record { to = ϕ₀ ; cong = ϕ-cong }
  ψ : ≈.Hom (F.F-ob (Colim D)) (Colim (F ∘ᴰ D))
  ψ = record { to = ψ₀ ; cong = ψ-cong }
  Xα : ≈.Algebra F
  Xα = record { X = Colim D ; α = θ ≈.∘ ψ }
  sat : Sat Xα Ξ
  sat e ξ = {!p!}
    -- where
    -- open Equation (Ξ e)
    -- p : Colim D [ assign Xα ξ (lhs (Ξ e)) ≈ assign Xα ξ (rhs (Ξ e)) ]
    -- p = joinTerms (≈psat e (λ v → tˡ (ξ v)) (≤≤ ∨ᶻ-l q) (≤≤ ∨ᶻ-r {!-l!}))
