{-# OPTIONS --type-in-type #-}
module QIT.Topology.Constructions where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Topology.Subset
open import QIT.Topology.Base
open import QIT.Topology.BishopReals

-- Disjoint sums
⨆ : (J : Set) → (J → Space _ _ _) → Space _ _ _
⨆ J Aᴶ = FreeSpace ⨆A 𝓞⨆A
  where
  open Space
  ⨆A = (Σ J λ j → ⟨ Aᴶ j ⟩)
  data 𝓞⨆A : 𝓟 ⨆A → Prop ℓ0 where
    sub : ∀ (j : J) (X : 𝓟 ⟨ Aᴶ j ⟩) (𝓞X : 𝓞 (Aᴶ j) X)
        → 𝓞⨆A (λ (i , x) → (i ≡ j) ∧ 𝓞 (Aᴶ j) X)

-- FIXME: Use category theoretic definition instead
-- ⨅ : (J : Set) → (J → Space _ _ _) → Space _ _ _
-- ⨅ J Aᴶ = FreeSpace ⨅A {!𝓞⨅A!}
--   where
--   open Space
--   ⨅A = (∀ j → ⟨ Aᴶ j ⟩)
--   data 𝓞⨅A : 𝓟 ⨅A → Prop ℓ0 where
--     sub : ∀ (j : J) (X : 𝓟 ⟨ Aᴶ j ⟩) (𝓞X : 𝓞 (Aᴶ j) X)
--         → 𝓞⨅A (λ f → {!!})
