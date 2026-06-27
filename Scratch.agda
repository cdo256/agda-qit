open import QIT.Prelude
open import QIT.Prop
open import QIT.Nat
open import QIT.Relation.SetQuotient

module Scratch where

module Tree
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ pathElim* : PathElim ⦄
  ⦃ setQuotients* : SetQuotients ⦄ where

  open import QIT.Setoid
  open import QIT.Setoid.Quotient
  
  data Tree : Set where
    l : ℕ → Tree
    n : Tree → Tree → Tree

  data _~_ : Tree → Tree → Prop where
    refl : ∀ {s} → s ~ s
    sym : ∀ {s t} → s ~ t → t ~ s
    trans : ∀ {s t u} → s ~ t → t ~ u → s ~ u
    pivot : ∀ s t u → n (n s t) u ~ n s (n t u)

  TreeSetoid : Setoid _ _
  TreeSetoid = record
    { Carrier = Tree
    ; _≈_ = _~_
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans } }

  Tree≈ = TreeSetoid /≈

  open SetoidQuotient TreeSetoid
