module QIT.Examples.PartialityMonad.ErasedEquiv where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Container.Indexed
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

open import QIT.Examples.PartialityMonad.Erased
open import QIT.Examples.PartialityMonad.ErasedW

Erased : I0 → Set
Erased iSeq0 = Seq0
Erased iPM0 = PM0
Erased i≤0 = ≤0
Erased i≈0 = ≈0

Seq0≅ : {!Seq0 ↔ ?!}
