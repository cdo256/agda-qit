{-# OPTIONS --type-in-type #-}
-- Basic foundations
open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset

-- Setoid theory
open import QIT.Setoid as ≈

-- QW machinery
open import QIT.QW.Signature

module QIT.QW.Initiality {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

private
  ℓD = ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

-- Container functor
open import QIT.Container.Base
open import QIT.Container.Functor S P ℓD ℓD'
open F-Ob

-- Size control and staging
open import QIT.Relation.Plump S P
open import QIT.QW.Stage sig
open import QIT.QW.Algebra sig
open import QIT.Setoid.Diagram ≤p

-- Colimits and cocontinuity
open import QIT.QW.Colimit ≤p ℓD ℓD' hiding (_≈ˡ_)
open import QIT.QW.Cocontinuity ≤p {ℓD} {ℓD'}

-- Module aliases for cleaner notation
module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)

-- Main theorem: cocontinuous functors give initial algebras
module _  where
  alg : Cocontinuous F D → ∥ Alg ∥
  alg ∣ cocont ∣ = ∣ record
    { alg = record
      { X = Colim D
      ; α = record
        { to = f
        ; cong = f-cong } }
    ; sat = {!!} } ∣
    where
    open ≈.Iso cocont
    f : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim D ⟩
    f (s , f) = sup (ιˢ s , λ i → f i .proj₁) , sup (s , λ i → f i .proj₂ .fst) , sup≤sup λ i → f i .proj₂ .snd
    f-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ] → Colim D [ f x ≈ f y ]
    f-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = begin
      (sup (ιˢ s , λ i → f i .proj₁) , sup (s , λ i → f i .proj₂ .fst) , sup≤sup λ i → f i .proj₂ .snd)
        ≈⟨ ≈lstep (sup≤sup λ _ → ∨ᶻ-l) (sup (s , λ i → f i .proj₂ .fst) , sup≤sup λ i → f i .proj₂ .snd) ⟩
      (sup (ιˢ s , λ i → f i .proj₁ ∨ᶻ g i .proj₁) , sup (s , λ i → f i .proj₂ .fst) , _)
        ≈⟨ ≈lstage _ (≈pcong s (λ i → f i .proj₁ ∨ᶻ g i .proj₁)
                               (λ i → f i .proj₂ .fst , ≤≤ ∨ᶻ-l {!sup≤sup!}) {!!} {!!}) ⟩
      (sup (ιˢ s , λ i → f i .proj₁ ∨ᶻ g i .proj₁) , sup (s , λ i → g i .proj₂ .fst) , _)
        ≈⟨ ≈lsym (≈lstep (sup≤sup λ _ → ∨ᶻ-r) (sup (s , λ i → g i .proj₂ .fst) , _)) ⟩
      (sup (ιˢ s , λ i → g i .proj₁) , sup (s , λ i → g i .proj₂ .fst) , sup≤sup λ i → g i .proj₂ .snd) ∎
      where open ≈.≈syntax {S = Colim D}
      
