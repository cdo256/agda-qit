module QIT.Examples.PartialityMonad.Erased where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

interleaved mutual
  data Seq0 : Set
  data A⊥0 : Set
  data ≤0 : Set
  data ≈0 : Set

  data _ where
    η0 : Bool → A⊥0
    ⊥0 : A⊥0
    ⨆0 : (a : Seq0) → A⊥0
    ⟦_⟧0 : Seq0 → ℕ → A⊥0
    _,0_ : (f : ℕ → A⊥0) → ((i : ℕ) → ≤0) → Seq0
    ≤refl0 : ∀ (x : A⊥0) → ≤0
    ≤trans0 : ∀ (x y z : A⊥0) → ≤0 → ≤0 → ≤0
    ⊥≤0 : ∀ (x : A⊥0) → ≤0
    ≤⨆0 : ∀ (a : Seq0) → ℕ → ≤0
    ⨆≤0 : ∀ (a : Seq0) (x : A⊥0) → (∀ (i : ℕ) → ≤0) → ≤0
    inc0 : (a : Seq0) → ∀ (i : ℕ) → ≤0
    ≈antisym0 : ∀ (x y : A⊥0) → ≤0 → ≤0 → ≈0
