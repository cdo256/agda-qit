open import QIT.Prelude
open import QIT.Prop

module QIT.Examples.Mobile.Cocontinuity (I : Set) where

open import QIT.Examples.Mobile.Base I
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Container.StrictFunctor Sᵀ Pᵀ (lsuc ℓ0)
open import QIT.Plump.Postulated Sᵀ Pᵀ as Z hiding (rec)
open import QIT.QW.Stage sig
import QIT.QW.Cocontinuity as QW

module C = QW sig

≡→≤ : ∀ {α β} → α ≡ β → α ≤ β
≡→≤ {α} {α} ≡.refl = ≤refl α

depth-preserving≤≥ : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → (ιᶻ (ŝ .fst) ≤ ιᶻ (t̂ .fst)) ∧ (ιᶻ (t̂ .fst) ≤ ιᶻ (ŝ .fst))
depth-preserving≤≥ α (s , s≤α) (t , t≤α) (≈pcong a μ f g r) =
    sup≤ (λ i → <sup i (p i .∧.fst))
  , sup≤ (λ i → <sup i (p i .∧.snd))
  where
  p : ∀ i → (ιᶻ (f i .fst) ≤ ιᶻ (g i .fst)) ∧ (ιᶻ (g i .fst) ≤ ιᶻ (f i .fst))
  p i = depth-preserving≤≥ (μ i) (f i) (g i) (r i)
depth-preserving≤≥ α (s , _) (t , _) (≈psat π ϕ _ _) =
    sup≤ (λ i → <sup (π⁻¹ i) (≡→≤ (≡.cong (λ ○ → ιᶻ (lower (ϕ ○))) (≡.sym (linv i)))))
  , sup≤ (λ i → <sup (π̂ i) (≤refl (ιᶻ (lower (ϕ (π̂ i))))))
  where
  open _↔_ π renaming (to to π̂; from to π⁻¹)
depth-preserving≤≥ α (s , s≤α) (s , t≤α) ≈prefl = ≤refl (ιᶻ s) , ≤refl (ιᶻ s)
depth-preserving≤≥ α (s , s≤α) (t , t≤α) (≈psym p) =
  let s≤t , t≤s = depth-preserving≤≥ α (t , t≤α) (s , s≤α) p
  in t≤s , s≤t
depth-preserving≤≥ α (s , s≤α) (t , t≤α) (≈ptrans {t̂ = u , u≤α} p q) =
  let s≤u , u≤s = depth-preserving≤≥ α (s , s≤α) (u , u≤α) p
      u≤t , t≤u = depth-preserving≤≥ α (u , u≤α) (t , t≤α) q
  in ≤≤ u≤t s≤u , ≤≤ u≤s t≤u
depth-preserving≤≥ α (s , s≤α) (t , t≤α) (≈pweaken {α = β} β≤α p) = depth-preserving≤≥ β _ _ p

depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≡ ιᶻ (t̂ .fst)
depth-preserving α ŝ t̂ p = ≤antisym s≤t t≤s
  where
  s≤t = depth-preserving≤≥ α ŝ t̂ p .∧.fst
  t≤s = depth-preserving≤≥ α ŝ t̂ p .∧.snd

cocontinuousIso = C.cocontinuous depth-preserving

cocontinuous : C.Cocontinuous F D
cocontinuous = ∣ cocontinuousIso ∣
