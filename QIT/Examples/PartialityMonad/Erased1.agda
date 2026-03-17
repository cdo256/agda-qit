module QIT.Examples.PartialityMonad.Erased1 where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

interleaved mutual
  data Seq0 : Set
  data PM0 : Set
  data ≤0 : Set
  data ≈0 : Set

  data _ where
    η0 : Bool → PM0
    ⊥0 : PM0
    ⨆0 : (a : Seq0) → PM0
    ⟦_⟧0 : Seq0 → ℕ → PM0
    _,0_ : (f : ℕ → PM0) → ((i : ℕ) → ≤0) → Seq0
    ≤refl0 : ∀ (x : PM0) → ≤0
    ≤trans0 : ∀ (x y z : PM0) → ≤0 → ≤0 → ≤0
    ⊥≤0 : ∀ (x : PM0) → ≤0
    ≤⨆0 : ∀ (a : Seq0) → ℕ → ≤0
    ⨆≤0 : ∀ (a : Seq0) (x : PM0) → (∀ (i : ℕ) → ≤0) → ≤0
    inc0 : (a : Seq0) → ∀ (i : ℕ) → ≤0
    ≈antisym0 : ∀ (x y : PM0) → ≤0 → ≤0 → ≈0
