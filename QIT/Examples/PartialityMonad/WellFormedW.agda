module QIT.Examples.PartialityMonad.WellFormedW where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

open import QIT.Container.Indexed
open import QIT.Examples.PartialityMonad.Erased

data I1 : Set where
  iA⊥1 : A⊥0 → I1
  i≤1 : A⊥0 → A⊥0 → ≤0 → I1
  i≈1 : A⊥0 → A⊥0 → ≈0 → I1

data S1 : I1 → Set where
  sη1 : (b : Bool) → S1 (iA⊥1 (η0 b))
  s⊥1 : S1 (iA⊥1 (⊥0))
  s⨆1 : ∀ a0 a-inc0 → S1 (iA⊥1 (⨆0 a0 a-inc0))
  s≤refl1 : ∀ x0
          → S1 (i≤1 x0 x0 (≤refl0 x0))
  s≤trans1 : ∀ x0 y0 z0
          → (p0 : ≤0) (q0 : ≤0)
          → S1 (i≤1 x0 z0 (≤trans0 x0 y0 z0 p0 q0))
  s⊥≤1 : ∀ x0
        → S1 (i≤1 ⊥0 x0 (⊥≤0 x0))
  s≤⨆1 : ∀ a0 a-inc0
        → (i : ℕ)
        → S1 (i≤1 (a0 i) (⨆0 a0 a-inc0) (≤⨆0 a0 a-inc0 i))
  s⨆≤1 : ∀ a0 a-inc0 x0
        → (p0 : (i : ℕ) → ≤0)
        → S1 (i≤1 (⨆0 a0 a-inc0) x0 (⨆≤0 x0 a0 a-inc0 p0))
  s≈antisym1 : ∀ x0 y0
              (p0 : ≤0) (q0 : ≤0)
            → S1 (i≈1 x0 y0 (≈antisym0 x0 y0 p0 q0))

data P1 : ∀ {i} → S1 i → Set where
  p⨆-a1 : ∀ a0 a-inc0
        → ℕ → P1 (s⨆1 a0 a-inc0)
  p⨆-a-inc1 : ∀ a0 a-inc0
            → ℕ → P1 (s⨆1 a0 a-inc0)
  p≤refl1-x1 : ∀ x0
             → P1 (s≤refl1 x0)
  p≤trans1-x1 : ∀ x0 y0 z0 p0 q0
              → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p≤trans1-y1 : ∀ x0 y0 z0 p0 q0
              → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p≤trans1-z1 : ∀ x0 y0 z0 p0 q0
              → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p≤trans1-p1 : ∀ x0 y0 z0 p0 q0
              → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p≤trans1-q1 : ∀ x0 y0 z0 p0 q0
              → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p⊥≤1-x1 : ∀ x0
          → P1 (s⊥≤1 x0)
  p≤⨆1-a1 : ∀ a0 a-inc0 i
          → ℕ → P1 (s≤⨆1 a0 a-inc0 i) 
  p≤⨆1-a-inc1 : ∀ a0 a-inc0 i
              → ℕ → P1 (s≤⨆1 a0 a-inc0 i) 
  p⨆≤1-a1 : ∀ a0 a-inc0 x0 p0
          → ℕ → P1 (s⨆≤1 a0 a-inc0 x0 p0) 
  p⨆≤1-a-inc1 : ∀ a0 a-inc0 x0 p0
              → ℕ → P1 (s⨆≤1 a0 a-inc0 x0 p0) 
  p⨆≤1-x1 : ∀ a0 a-inc0 x0 p0
          → P1 (s⨆≤1 a0 a-inc0 x0 p0) 
  p⨆≤1-p1 : ∀ a0 a-inc0 x0 p0
          → ℕ → P1 (s⨆≤1 a0 a-inc0 x0 p0) 
  p≈antisym1-x1 : ∀ x0 y0 p0 q0
                → P1 (s≈antisym1 x0 y0 p0 q0)
  p≈antisym1-y1 : ∀ x0 y0 p0 q0
                → P1 (s≈antisym1 x0 y0 p0 q0)
  p≈antisym1-p1 : ∀ x0 y0 p0 q0
                → P1 (s≈antisym1 x0 y0 p0 q0)
  p≈antisym1-q1 : ∀ x0 y0 p0 q0
                → P1 (s≈antisym1 x0 y0 p0 q0)

child1 : ∀ {i} {s1 : S1 i} → P1 s1 → I1
child1 (p⨆-a1 a0 a-inc0 j) = iA⊥1 (a0 j)
child1 (p⨆-a-inc1 a0 a-inc0 j) = i≤1 (a0 j) (a0 (suc j)) (a-inc0 j)
child1 (p≤refl1-x1 x0) = iA⊥1 x0
child1 (p≤trans1-x1 x0 y0 z0 p0 q0) = iA⊥1 x0
child1 (p≤trans1-y1 x0 y0 z0 p0 q0) = iA⊥1 y0
child1 (p≤trans1-z1 x0 y0 z0 p0 q0) = iA⊥1 z0
child1 (p≤trans1-p1 x0 y0 z0 p0 q0) = i≤1 x0 y0 p0
child1 (p≤trans1-q1 x0 y0 z0 p0 q0) = i≤1 y0 z0 q0
child1 (p⊥≤1-x1 x0) = iA⊥1 x0
child1 (p≤⨆1-a1 a0 a-inc0 i j) = iA⊥1 (a0 j)
child1 (p≤⨆1-a-inc1 a0 a-inc0 i j) = i≤1 (a0 j) (a0 (suc j)) (a-inc0 j)
child1 (p⨆≤1-a1 a0 a-inc0 x0 p0 j) = iA⊥1 (a0 j)
child1 (p⨆≤1-a-inc1 a0 a-inc0 x0 p0 j) = i≤1 (a0 j) (a0 (suc j)) (a-inc0 j)
child1 (p⨆≤1-x1 a0 a-inc0 x0 p0) = iA⊥1 x0
child1 (p⨆≤1-p1 a0 a-inc0 x0 p0 j) = i≤1 (a0 j) (a0 (suc j)) (a-inc0 j)
child1 (p≈antisym1-x1 x0 y0 p0 q0) = iA⊥1 x0
child1 (p≈antisym1-y1 x0 y0 p0 q0) = iA⊥1 y0
child1 (p≈antisym1-p1 x0 y0 p0 q0) = i≤1 x0 y0 p0
child1 (p≈antisym1-q1 x0 y0 p0 q0) = i≤1 y0 x0 q0

Cont1 : ICont I1
Cont1 = icont S1 P1 child1

W1 : I1 → Set
W1 = IW Cont1

PM = Σ I1 W1

A⊥ : Set
A⊥ = Σ A⊥0 λ x0 → W1 (iA⊥1 x0)

_≤_ : A⊥ → A⊥ → Set
(x0 , x1) ≤ (y0 , y1) = Σ ≤0 λ p0 → W1 (i≤1 x0 y0 p0)

_≈_ : A⊥ → A⊥ → Set
(x0 , x1) ≈ (y0 , y1) = Σ ≈0 λ p0 → W1 (i≈1 x0 y0 p0)

⊥ : A⊥
⊥ = ⊥0 , isup _ (s⊥1 , λ ())
