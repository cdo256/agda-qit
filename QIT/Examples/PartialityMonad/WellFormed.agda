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
  data Seq1 : Seq0 → Set
  data A⊥1 : A⊥0 → Set
  data _≤1_⊣_ : A⊥0 → A⊥0 → ≤0 → Set
  data _≈1_⊣_ : A⊥0 → A⊥0 → ≈0 → Set

  data _ where
    η1 : (b : Bool) → A⊥1 (η0 b)
    ⊥1 : A⊥1 ⊥0
    ⨆1 : ∀ {a0}
       → Seq1 a0
       → A⊥1 (⨆0 a0)
    ⟦_⟧1 : ∀ {a0}
         → Seq1 a0
         → (n : ℕ)
         → A⊥1 (⟦ a0 ⟧0 n)
    ,1 : (f0   : ℕ → A⊥0)
         → (f0≤  : (i : ℕ) → ≤0)
         → (f1   : (i : ℕ) → A⊥1 (f0 i))
         → (f1≤  : (i : ℕ) → f0 i ≤1 f0 (suc i) ⊣ f0≤ i)
         → Seq1 (f0 ,0 f0≤)
    ≤refl1 : ∀ {x0}
           → A⊥1 x0
           → x0 ≤1 x0 ⊣ ≤refl0 x0
    ≤trans1 : ∀ {x0 y0 z0}
             {p0 : ≤0} {q0 : ≤0}
           → x0 ≤1 y0 ⊣ p0
           → y0 ≤1 z0 ⊣ q0
           → x0 ≤1 z0 ⊣ ≤trans0 x0 y0 z0 p0 q0
    ⊥≤1 : ∀ {x0}
         → A⊥1 x0
         → ⊥0 ≤1 x0 ⊣ ⊥≤0 x0
    ≤⨆1 : ∀ {a0}
         → (a1 : Seq1 a0)
         → (i : ℕ)
         → ⟦ a0 ⟧0 i ≤1 ⨆0 a0 ⊣ ≤⨆0 a0 i
    ⨆≤1 : ∀ {a0 x0}
         → (a1 : Seq1 a0)
         → (x1 : A⊥1 x0)
         → (p0 : (i : ℕ) → ≤0)
         → ((i : ℕ) → ⟦ a0 ⟧0 i ≤1 x0 ⊣ p0 i)
         → ⨆0 a0 ≤1 x0 ⊣ ⨆≤0 a0 x0 p0
    inc1 : ∀ {a0}
         → (a1 : Seq1 a0)
         → (i : ℕ)
         → ⟦ a0 ⟧0 i ≤1 ⟦ a0 ⟧0 (suc i) ⊣ inc0 a0 i
    ≈antisym1 : ∀ {x0 y0}
               {p0 : ≤0} {q0 : ≤0}
             → x0 ≤1 y0 ⊣ p0
             → y0 ≤1 x0 ⊣ q0
             → x0 ≈1 y0 ⊣ ≈antisym0 x0 y0 p0 q0
