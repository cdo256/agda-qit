module QIT.Examples.PartialityMonad.Erased where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

interleaved mutual
  data A⊥0 : Set
  data ≤0 : Set
  data ≈0 : Set

  data _ where
    η0 : Bool → A⊥0
    ⊥0 : A⊥0
    ⨆0 : (a0 : ℕ → A⊥0) (a-inc0 : ℕ → ≤0) → A⊥0
    ≤refl0 : (x0 : A⊥0) → ≤0
    ≤trans0 : (x0 y0 z0 : A⊥0) (p q : ≤0) → ≤0
    ⊥≤0 : (x0 : A⊥0) → ≤0
    ≤⨆0 : (a0 : ℕ → A⊥0) (a-inc0 : ℕ → ≤0) (i : ℕ) → ≤0
    ⨆≤0 : (x0 : A⊥0) (a0 : ℕ → A⊥0) (a-inc0 : ℕ → ≤0) (p0 : ℕ → ≤0) → ≤0
    ≈antisym0 : (x y : A⊥0) (p0 q0 : ≤0) → ≈0
