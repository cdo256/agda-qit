module QIT.Examples.PartialityMonad.WellFormed where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

open import QIT.Examples.PartialityMonad.Erased

interleaved mutual
  data A⊥1 : A⊥0 → Set
  data _≤1_⊣_ : A⊥0 → A⊥0 → ≤0 → Set
  data _≈1_⊣_ : A⊥0 → A⊥0 → ≈0 → Set

  data _ where
    η1 : (b : Bool) → A⊥1 (η0 b)
    ⊥1 : A⊥1 ⊥0
    ⨆1 : ∀ {a0 a-inc0}
       → (∀ i → A⊥1 (a0 i))
       → (∀ i → a0 i ≤1 a0 (suc i) ⊣ a-inc0 i)
       → A⊥1 (⨆0 a0 a-inc0)
    ≤refl1 : ∀ {x0}
           → A⊥1 x0
           → x0 ≤1 x0 ⊣ ≤refl0 x0
    ≤trans1 : ∀ {x0 y0 z0 p0 q0}
           → A⊥1 x0
           → A⊥1 y0
           → A⊥1 z0
           → x0 ≤1 y0 ⊣ p0
           → y0 ≤1 z0 ⊣ q0
           → x0 ≤1 z0 ⊣ ≤trans0 x0 y0 z0 p0 q0
    ⊥≤1 : ∀ {x0}
         → A⊥1 x0
         → ⊥0 ≤1 x0 ⊣ ⊥≤0 x0
    ≤⨆1 : ∀ {a0 a-inc0}
         → (∀ i → A⊥1 (a0 i))
         → (∀ i → a0 i ≤1 a0 (suc i) ⊣ a-inc0 i)
         → (j : ℕ)
         → a0 j ≤1 ⨆0 a0 a-inc0 ⊣ ≤⨆0 a0 a-inc0 j
    ⨆≤1 : ∀ {x0 a0 a-inc0 p0}
         → (A⊥1 x0)
         → (∀ i → A⊥1 (a0 i))
         → (∀ i → a0 i ≤1 a0 (suc i) ⊣ a-inc0 i)
         → ((i : ℕ) → a0 i ≤1 x0 ⊣ p0 i)
         → ⨆0 a0 a-inc0 ≤1 x0 ⊣ ⨆≤0 x0 a0 a-inc0 p0
    ≈antisym1 : ∀ {x0 y0 p0 q0}
              → A⊥1 x0
              → A⊥1 y0
              → x0 ≤1 y0 ⊣ p0
              → y0 ≤1 x0 ⊣ q0
              → x0 ≈1 y0 ⊣ ≈antisym0 x0 y0 p0 q0
