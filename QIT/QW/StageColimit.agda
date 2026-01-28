

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

module QIT.QW.StageColimit {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
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

-- Module aliases for cleaner notation
module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)

T = W S P
αˡ : ⟨ Colim D ⟩ → Z
αˡ (α , t , t≤α) = α
tˡ : ⟨ Colim D ⟩ → T
tˡ (α , t , t≤α) = t
t≤αˡ : (x : ⟨ Colim D ⟩) → tˡ x ≤ᵀ αˡ x
t≤αˡ (α , t , t≤α) = t≤α

joinTerms : ∀ {x y : ⟨ Colim D ⟩}
          → αˡ x ∨ᶻ αˡ y ⊢ (tˡ x , ≤≤ ∨ᶻ-l (t≤αˡ x)) ≈ᵇ (tˡ y , ≤≤ ∨ᶻ-r (t≤αˡ y))
          → Colim D [ x ≈ y ]
joinTerms {α , s , s≤α} {β , t , t≤β} p =
  begin
    (α , s , s≤α)
      ≈⟨ ≈lstep ∨ᶻ-l (s , _) ⟩
    (α ∨ᶻ β , (s , _))
      ≈⟨ ≈lstage _ p ⟩
    (α ∨ᶻ β , (t , _))
      ≈⟨ ≈lsym (≈lstep ∨ᶻ-r (t , _)) ⟩
    (β , t , t≤β) ∎
  where
  open ≈.Hom
  open Setoid (Colim D)
  open ≈.≈syntax {S = Colim D}
