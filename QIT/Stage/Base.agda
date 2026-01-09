open import QIT.Prelude
open import QIT.QW.Signature

module QIT.Stage.Base {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where

open Sig sig

open import Data.Product hiding (∃)

open import QIT.Container.Base
open import QIT.Relation.Plump S P
open import QIT.Relation.Subset

private
  T = W S P

D₀ : (α : Z) → Set (ℓS ⊔ ℓP)
D₀ α = ΣP T (_≤ᵀ α)

psup : ∀ a μ (f : ∀ i → D₀ (μ i)) → D₀ (sup (ιˢ a , μ))
psup a μ f = sup (a , λ i → f i .fst) , sup≤ (λ i → <sup i (f i .snd))

pweaken : ∀ {α β} → α ≤ β → D₀ α → D₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α
