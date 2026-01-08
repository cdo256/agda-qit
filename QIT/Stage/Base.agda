open import QIT.Prelude

module QIT.Stage.Base {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import Data.Product hiding (∃)

open import QIT.Container.Base
open import QIT.Relation.Plump S P
open import QIT.Relation.Subset

private
  T = W S P

P₀ : (α : Z) → Set (ℓS ⊔ ℓP)
P₀ α = ΣP T (_≤ᵀ α)

psup : ∀ a μ (f : ∀ i → P₀ (μ i)) → P₀ (sup (ιˢ a , μ))
psup a μ f = sup (a , λ i → f i .fst) , sup≤ (λ i → <sup i (f i .snd))

pweaken : ∀ {α β} → α ≤ β → P₀ α → P₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α
