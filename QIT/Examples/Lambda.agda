module QIT.Examples.Lambda where

open import QIT.Prelude
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_)

infixl 15 _﹫_
infixl 30 _[_]

data Λ : ℕ → Set where
  ν : ∀ {n} → Fin n → Λ n
  _﹫_ : ∀ {n} → Λ n → Λ n → Λ n
  λ̂_ : ∀ {n} → Λ (suc n) → Λ n

reindex : ∀ {n} → Λ n → Λ (suc n)
reindex {n} (ν i) = ν (suc i)
reindex {n} (t ﹫ u) = reindex t ﹫ reindex u
reindex {n} (λ̂ t) = λ̂ reindex t

_[_] : ∀ {n m} → Λ n → (σ : Fin n → Λ m) → Λ m
ν i [ σ ] = σ i
(t ﹫ u) [ σ ] = t [ σ ] ﹫ u [ σ ] 
_[_] {n} {m} (λ̂ s) σ = λ̂ (s [ σ' ])
  where
  σ' : Fin (suc n) → Λ (suc m)
  σ' zero = ν zero
  σ' (suc i) = reindex (σ i)

v0 : ∀ {n} → Λ (1 + n)
v0 = ν zero
v1 : ∀ {n} → Λ (2 + n)
v1 = ν (suc zero)
v2 : ∀ {n} → Λ (3 + n)
v2 = ν (suc (suc zero))

module Example1 where
  I : ∀ {n} → Λ n
  I = λ̂ v0 

  K : ∀ {n} → Λ n
  K = λ̂ λ̂ v1

  S : ∀ {n} → Λ n
  S = λ̂ λ̂ λ̂ ((v2 ﹫ v1) ﹫ (v2 ﹫ v0))

module Compute where
  β-subst : ∀ {n} → Λ (suc n) → Λ n → Λ n
  β-subst {n} s t = s [ σ ]
    where
    σ : Fin (suc n) → Λ n
    σ zero = t
    σ (suc a) = ν a

  infix 5 _≫_
  data _≫_ : ∀ {n} → Λ n → Λ n → Set where
    β≫ : ∀ {n} → (s : Λ (suc n)) (t : Λ n) → ((λ̂ s) ﹫ t) ≫ β-subst s t
    ﹫≫₁ : ∀ {n} → (s s' : Λ n) (t : Λ n) → s ≫ s' → (s ﹫ t) ≫ (s' ﹫ t)
    ﹫≫₂ : ∀ {n} → (s : Λ n) (t t' : Λ n) → t ≫ t' → (s ﹫ t) ≫ (s ﹫ t')
    Λ≫ : ∀ {n} → (s t : Λ (suc n)) → s ≫ t → λ̂ s ≫ λ̂ t

module Monad5 where
  fmax : ∀ {n} → Fin (suc n)
  fmax {zero}  = zero
  fmax {suc n} = suc fmax

  -- Embed a level from a smaller context into a larger context.
  embˡ : ∀ {m n} → m ≤ n → Fin m → Fin n
  embˡ {zero}    {n}     z≤n     ()
  embˡ {suc m}   {suc n} (s≤s p) zero    = zero
  embˡ {suc m}   {suc n} (s≤s p) (suc i) = suc (embˡ p i)

  -- Convert a de Bruijn level to a de Bruijn index.
  -- Example in context size 3:
  --   level 0 ↦ index 2
  --   level 1 ↦ index 1
  --   level 2 ↦ index 0
  level→index : ∀ {n} → Fin n → Fin n
  level→index {zero}  ()
  level→index {suc n} zero    = fmax
  level→index {suc n} (suc i) = inject₁ (level→index i)

  -- A variable born in context `birth`, currently being used in context `now`.
  record Var (birth now : ℕ) : Set where
    constructor v_at_
    field
      level : Fin birth
      valid : birth ≤ now

  open Var public

  -- Weakening for variables: a variable remains valid in deeper contexts.
  wkVar : ∀ {birth now} → Var birth now → Var birth (suc now)
  wkVar {birth} {now} (v i at p) = v i at ≤-trans p (n≤1+n now)

  ↑ : ∀ {birth now} (m : ℕ) → Var birth now → Var birth (m + now)
  ↑ zero (v i at p) = v i at p
  ↑ (suc m) (v i at p) = wkVar (↑ m (v i at p))

  -- Interpret a variable as a term in the current context.
  v▹ : ∀ {birth now} → Var birth now → Λ now
  v▹ (v i at p) = ν (level→index (embˡ p i))

  -- Binder form: introduces a fresh variable born in the extended context.
  λ▹_ : ∀ {n} → (Var (suc n) (suc n) → Λ (suc n)) → Λ n
  λ▹_ {n} s = λ̂ (s (v (fromℕ n) at ≤-refl))

  I : ∀ {n} → Λ n
  I = λ▹ λ x → v▹ x

  K : ∀ {n} → Λ n
  K = λ▹ λ x → λ▹ λ y → v▹ (↑ 1 x)

  S : ∀ {n} → Λ n
  S = λ▹ λ x → λ▹ λ y → λ▹ λ z →
        ((v▹ (↑ 2 x)) ﹫ v▹ z) ﹫
        ((v▹ (↑ 1 y)) ﹫ v▹ z)
