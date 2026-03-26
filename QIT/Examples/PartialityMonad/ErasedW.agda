module QIT.Examples.PartialityMonad.ErasedW where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Container.Indexed
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

data I0 : Set where
  iSeq0 : I0
  iA⊥0 : I0
  i≤0 : I0
  i≈0 : I0

data S0 : I0 → Set where
  sη0        : Bool → S0 iA⊥0
  s⊥0        : S0 iA⊥0
  s⨆0        : S0 iA⊥0
  s⟦⟧0       : ℕ → S0 iA⊥0
  s,0        : S0 iSeq0
  s≤refl0    : S0 i≤0
  s≤trans0   : S0 i≤0
  s⊥≤0       : S0 i≤0
  s≤⨆0       : ℕ → S0 i≤0
  s⨆≤0       : S0 i≤0
  sinc0      : ℕ → S0 i≤0
  s≈antisym0 : S0 i≈0

data P0 : ∀ {i} → S0 i → Set where
  p⨆-seq        : P0 s⨆0
  p⟦⟧-seq       : ∀ {n} → P0 (s⟦⟧0 n)

  p,0-pm        : ℕ → P0 s,0
  p,0-≤         : ℕ → P0 s,0

  p≤refl-x      : P0 s≤refl0

  p≤trans-x     : P0 s≤trans0
  p≤trans-y     : P0 s≤trans0
  p≤trans-z     : P0 s≤trans0
  p≤trans-p     : P0 s≤trans0
  p≤trans-q     : P0 s≤trans0

  p⊥≤-x         : P0 s⊥≤0

  p≤⨆-seq       : ∀ {n} → P0 (s≤⨆0 n)

  p⨆≤-seq       : P0 s⨆≤0
  p⨆≤-x         : P0 s⨆≤0
  p⨆≤-step      : ℕ → P0 s⨆≤0

  pinc-seq      : ∀ {n} → P0 (sinc0 n)

  p≈antisym-x     : P0 s≈antisym0
  p≈antisym-y     : P0 s≈antisym0
  p≈antisym-p     : P0 s≈antisym0
  p≈antisym-q     : P0 s≈antisym0

child0 : ∀ {i} {s : S0 i} → P0 s → I0
child0 p⨆-seq          = iSeq0
child0 p⟦⟧-seq         = iSeq0

child0 (p,0-pm _)      = iA⊥0
child0 (p,0-≤  _)      = i≤0

child0 p≤refl-x        = iA⊥0

child0 p≤trans-x       = iA⊥0
child0 p≤trans-y       = iA⊥0
child0 p≤trans-z       = iA⊥0
child0 p≤trans-p       = i≤0
child0 p≤trans-q       = i≤0

child0 p⊥≤-x           = iA⊥0

child0 p≤⨆-seq         = iSeq0

child0 p⨆≤-seq         = iSeq0
child0 p⨆≤-x           = iA⊥0
child0 (p⨆≤-step _)    = i≤0

child0 pinc-seq        = iSeq0

child0 p≈antisym-x     = iA⊥0
child0 p≈antisym-y     = iA⊥0
child0 p≈antisym-p     = i≤0
child0 p≈antisym-q     = i≤0

C0 : ICont I0
C0 = icont S0 P0 child0

W0 : I0 → Set
W0 = IW C0
