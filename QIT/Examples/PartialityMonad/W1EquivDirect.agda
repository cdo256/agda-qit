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
open import QIT.Examples.PartialityMonad.WellFormedW 
import QIT.Examples.PartialityMonad.Direct as D

data DR : Set where
  dA⊥ : D.A⊥ → DR
  dSeq : D.Seq → DR
  d≤ : (x y : D.A⊥) → x D.≤ y → DR
  d≈ : (x y : D.A⊥) → x D.≈ y → DR

D→W : DR → PM
D→W (dA⊥ (D.η b)) = iA⊥1 (η0 b) , isup _ (sη1 b , λ ())
D→W (dA⊥ D.⊥) = iA⊥1 ⊥0 , isup _ (s⊥1 , λ ())
D→W (dA⊥ (D.⨆ a)) = {!!}
D→W (dA⊥ (D.⟦ x ⟧ x₁)) = {!!}
D→W (dSeq x) = {!!}
D→W (d≤ x y p) = {!!}
D→W (d≈ x y p) = {!!}
