
open import QIT.Prelude

module QIT.Mobile.Cocontinuity (I : Set) where

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Mobile.Base I
open import QIT.Setoid as ≈
open import QIT.Container.Base
open import QIT.Relation.Plump Sᵀ Pᵀ
open import QIT.Setoid.Diagram ≤p

open import QIT.QW.Colimit ≤p ℓ0 (lsuc ℓ0) hiding (_≈ˡ_)
open import QIT.QW.Cocontinuity sig using (depthPrserving→cocontinuous; Cocontinuous)
open import QIT.QW.Stage sig
open import QIT.QW.StageColimit sig using (joinTerms; αˡ; tˡ; t≤αˡ)

open import QIT.Container.Functor Sᵀ Pᵀ ℓ0 (lsuc ℓ0)

open F-Ob

module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)

depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≤≥ ιᶻ (t̂ .fst)
depth-preserving α (s , s≤α) (t , t≤α) (≈pcong a μ f g r) =
    sup≤sup (λ i → p i .∧.fst) , sup≤sup (λ i → p i .∧.snd)
  where p : ∀ i → ιᶻ (f i .fst) ≤≥ ιᶻ (g i .fst)
        p i = depth-preserving (μ i) (f i) (g i) (r i)
depth-preserving α (s , _) (t , _) (≈psat π ϕ _ _) =
    sup≤ (λ i → <sup (π⁻¹ i) (≡→≤ (≡.cong (λ ○ → ιᶻ (lower (ϕ ○))) (≡.sym (linv i)))))
  , sup≤ (λ i → <sup (π̂ i) (≤refl (ιᶻ (lower (ϕ (π̂ i))))))
  where
  open _↔_ π renaming (to to π̂; from to π⁻¹)
depth-preserving α (s , s≤α) (s , t≤α) ≈prefl = ≤refl (ιᶻ s) , ≤refl (ιᶻ s)
depth-preserving α (s , s≤α) (t , t≤α) (≈psym p) =
  let s≤t , t≤s = depth-preserving α (t , t≤α) (s , s≤α) p
  in t≤s , s≤t
depth-preserving α (s , s≤α) (t , t≤α) (≈ptrans {t̂ = u , u≤α} p q) =
  let s≤u , u≤s = depth-preserving α (s , s≤α) (u , u≤α) p
      u≤t , t≤u = depth-preserving α (u , u≤α) (t , t≤α) q
  in ≤≤ u≤t s≤u , ≤≤ u≤s t≤u
depth-preserving α (s , s≤α) (t , t≤α) (≈pweaken {α = β} β≤α p) = depth-preserving β _ _ p

cocontinuous : Cocontinuous F D
cocontinuous = depthPrserving→cocontinuous depth-preserving
