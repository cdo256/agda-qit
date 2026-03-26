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
  iSeq1 : Seq0 → I1
  iA⊥1 : A⊥0 → I1
  i≤1 : A⊥0 → A⊥0 → ≤0 → I1
  i≈1 : A⊥0 → A⊥0 → ≈0 → I1

data S1 : I1 → Set where
  sη1 : (b : Bool) → S1 (iA⊥1 (η0 b))
  s⊥1 : S1 (iA⊥1 (⊥0))
  s⨆1 : ∀ (a0 : Seq0) → S1 (iA⊥1 (⨆0 a0))
  s⟦⟧1 : ∀ a0 → (n : ℕ) → S1 (iA⊥1 (⟦ a0 ⟧0 n))
  s,1 : (f0 : ℕ → A⊥0)
      → (f0≤ : (i : ℕ) → ≤0)
      → S1 (iSeq1 (f0 ,0 f0≤))
  s≤refl1 : ∀ x0
          → S1 (i≤1 x0 x0 (≤refl0 x0))
  s≤trans1 : ∀ x0 y0 z0
          → (p0 : ≤0) (q0 : ≤0)
          → S1 (i≤1 x0 z0 (≤trans0 x0 y0 z0 p0 q0))
  s⊥≤1 : ∀ x0
        → S1 (i≤1 ⊥0 x0 (⊥≤0 x0))
  s≤⨆1 : ∀ a0
        → (i : ℕ)
        → S1 (i≤1 (⟦ a0 ⟧0 i) (⨆0 a0) (≤⨆0 a0 i))
  s⨆≤1 : ∀ a0 x0
        → (p0 : (i : ℕ) → ≤0)
        → S1 (i≤1 (⨆0 a0) x0 (⨆≤0 a0 x0 p0))
  sinc1 : ∀ a0
        → (i : ℕ)
        → S1 (i≤1 (⟦ a0 ⟧0 i) (⟦ a0 ⟧0 (suc i)) (inc0 a0 i))
  s≈antisym1 : ∀ x0 y0
              (p0 : ≤0) (q0 : ≤0)
            → S1 (i≈1 x0 y0 (≈antisym0 x0 y0 p0 q0))

data P1 : ∀ {i} → S1 i → Set where
  p⨆-a1 : ∀ a0 → P1 (s⨆1 a0)
  p⟦⟧-a1 : ∀ a0 (n : ℕ) → P1 (s⟦⟧1 a0 n)
  p,1-f1  : ∀ (f0 : ℕ → A⊥0) (f0≤ : (i : ℕ) → ≤0)
          → (i : ℕ)
          → P1 (s,1 f0 f0≤)
  p,1-f≤1 : ∀ (f0 : ℕ → A⊥0) (f0≤ : (i : ℕ) → ≤0)
          → (i : ℕ)
          → P1 (s,1 f0 f0≤)
  p≤refl1-x1 : ∀ (x0 : A⊥0)
             → P1 (s≤refl1 x0)
  p≤trans1-p1 : ∀ (x0 y0 z0 : A⊥0)
          → (p0 : ≤0) (q0 : ≤0)
          → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p≤trans1-q1 : ∀ (x0 y0 z0 : A⊥0)
          → (p0 : ≤0) (q0 : ≤0)
          → P1 (s≤trans1 x0 y0 z0 p0 q0)
  p⊥≤1-x1 : ∀ (x0 : A⊥0)
       → P1 (s⊥≤1 x0)
  p≤⨆1-a1 : ∀ (a0 : Seq0) (i : ℕ)
       → P1 (s≤⨆1 a0 i) 
  p⨆≤1-a1 : ∀ a0 x0
        → (p0 : (i : ℕ) → ≤0)
       → P1 (s⨆≤1 a0 x0 p0) 
  p⨆≤1-x1 : ∀ a0 x0
          → (p0 : (i : ℕ) → ≤0)
          → P1 (s⨆≤1 a0 x0 p0) 
  p⨆≤1-≤1 : ∀ a0 x0
          → (p0 : (i : ℕ) → ≤0)
          → (i : ℕ)
          → P1 (s⨆≤1 a0 x0 p0) 
  pinc1-a1 : ∀ a0
           → (i : ℕ)
           → P1 (sinc1 a0 i)
  p≈antisym1-p1 : ∀ (x0 y0 : A⊥0)
            (p0 : ≤0) (q0 : ≤0)
          → P1 (s≈antisym1 x0 y0 p0 q0)
  p≈antisym1-q1 : ∀ (x0 y0 : A⊥0)
          → (p0 : ≤0) (q0 : ≤0)
          → P1 (s≈antisym1 x0 y0 p0 q0)

child1 : ∀ {i} {s1 : S1 i} → P1 s1 → I1
child1 (p⨆-a1 a0) = iSeq1 a0
child1 (p⟦⟧-a1 a0 i) = iSeq1 a0
child1 (p,1-f1 f0 f≤0 i) = iA⊥1 (f0 i)
child1 (p,1-f≤1 f0 f≤0 i) = i≤1 (f0 i) (f0 (suc i)) (f≤0 i)
child1 (p≤refl1-x1 x0) = iA⊥1 x0
child1 (p≤trans1-p1 x0 y0 z0 p0 q0) = i≤1 x0 y0 p0
child1 (p≤trans1-q1 x0 y0 z0 p0 q0) = i≤1 y0 z0 q0
child1 (p⊥≤1-x1 x0) = iA⊥1 x0
child1 (p≤⨆1-a1 a0 i) = iSeq1 a0
child1 (p⨆≤1-a1 a0 x0 p0) = iSeq1 a0
child1 (p⨆≤1-x1 a0 x0 p0) = iA⊥1 x0
child1 (p⨆≤1-≤1 a0 x0 p0 i) = i≤1 (⟦ a0 ⟧0 i) x0 (p0 i)
child1 (pinc1-a1 a0 i) = iSeq1 a0
child1 (p≈antisym1-p1 x0 y0 p0 q0) = i≤1 x0 y0 p0
child1 (p≈antisym1-q1 x0 y0 p0 q0) = i≤1 y0 x0 q0

Cont1 : ICont I1
Cont1 = icont S1 P1 child1

W1 : I1 → Set
W1 = IW Cont1

PM = Σ I1 W1

A⊥ : Set
A⊥ = Σ A⊥0 λ x0 → W1 (iA⊥1 x0)

Seq : Set
Seq = Σ Seq0 λ a0 → W1 (iSeq1 a0)

_≤_ : A⊥ → A⊥ → Set
(x0 , x1) ≤ (y0 , y1) = Σ ≤0 λ p0 → W1 (i≤1 x0 y0 p0)

_≈_ : A⊥ → A⊥ → Set
(x0 , x1) ≈ (y0 , y1) = Σ ≈0 λ p0 → W1 (i≈1 x0 y0 p0)

⊥ : A⊥
⊥ = ⊥0 , isup _ (s⊥1 , λ ())
