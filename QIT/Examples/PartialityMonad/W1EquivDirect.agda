module QIT.Examples.PartialityMonad.W1EquivDirect where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

open import QIT.Container.Indexed
open import QIT.Examples.PartialityMonad.Erased
open import QIT.Examples.PartialityMonad.WellFormedW renaming (PM to W)
import QIT.Examples.PartialityMonad.Direct as D

data DR : Set where
  dA⊥ : D.A⊥ → DR
  d≤ : (x y : D.A⊥) → x D.≤ y → DR
  d≈ : (x y : D.A⊥) → x D.≈ y → DR

-- module D→W where
--   fA⊥ : D.A⊥ → A⊥
--   fSeq : D.Seq → Seq
--   f≤ : ∀ x y → x D.≤ y → fA⊥ x ≤ fA⊥ y
--   f≈ : ∀ x y → x D.≈ y → fA⊥ x ≈ fA⊥ y
--   fA⊥ (D.η b) = η0 b , isup _ (sη1 b , λ ())
--   fA⊥ D.⊥ = ⊥0 , isup _ (s⊥1 , λ ())
--   fA⊥ (D.⨆ a) = ⨆0 {!!} , {!!}
--   fA⊥ (D.⟦ x ⟧ x₁) = {!!}

--   -- A⊥-red (D.η x) = {!!}
--   -- A⊥-red D.⊥ = {!!}
--   -- A⊥-red (D.⨆ a) = {!!}
--   -- A⊥-red (D.⟦ x ⟧ x₁) = {!!}


--   -- D→W : DR → W
--   -- D→W (dA⊥ (D.η b)) = iA⊥1 (η0 b) , isup _ (sη1 b , λ ())
--   -- D→W (dA⊥ D.⊥) = iA⊥1 ⊥0 , isup _ (s⊥1 , λ ())
--   -- D→W (dA⊥ (D.⨆ a)) = iA⊥1 (⨆0 {!!}) , {!!}
--   -- D→W (dA⊥ (D.⟦ x ⟧ x₁)) = {!!}
--   -- D→W (dSeq x) = {!!}
--   -- D→W (d≤ x y p) = {!!}
--   -- D→W (d≈ x y p) = {!!}
