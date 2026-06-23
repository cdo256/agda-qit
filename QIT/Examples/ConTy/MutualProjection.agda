{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude

module QIT.Examples.ConTy.MutualProjection ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

record Algebra' : Set₁ where
  field
    C : Set
    P : Set


record Algebra : Set₁ where
  field
    C : Set
    T : Set
    W : T → C → Set

    ∙ : C
    ▷ : (γ : C) (a : T) (w : W a γ) → C
    ▷p : (γ : C) (a : T) (w : W a γ)
       → {!!}
    -- k▷ : (γ : CT) (a : CT)
    --   → (kγ : [ γ ] ≡ ĉ)
    --   → (ka : [ a ] ≡ t̂ γ)
    --   → [ ▷ γ a ] ≡ ĉ
    -- u : (γ : CT) → CT
    -- ku : (γ : CT)
    --   → (kγ : [ γ ] ≡ ĉ)
    --   → [ u γ ] ≡ t̂ γ 
    -- π : (γ : CT) (a : CT) (b : CT) → CT
    -- kπ : (γ : CT) (a : CT) (b : CT) 
    --   → (kγ : [ γ ] ≡ ĉ)
    --   → (ka : [ a ] ≡ t̂ γ)
    --   → (kb : [ b ] ≡ t̂ (▷ γ a))
    --   → [ π γ a b ] ≡ t̂ γ 
    -- σ : (γ : CT) (a : CT) (b : CT) → CT
    -- kσ : (γ : CT) (a : CT) (b : CT) 
    --   → (kγ : [ γ ] ≡ ĉ)
    --   → (ka : [ a ] ≡ t̂ γ)
    --   → (kb : [ b ] ≡ t̂ (▷ γ a))
    --   → [ σ γ a b ] ≡ t̂ γ 
    -- σ▷ : (γ : CT) (a : CT) (b : CT) (c : CT) 
    --   → (kγ : [ γ ] ≡ ĉ)
    --   → (ka : [ a ] ≡ t̂ γ)
    --   → (kb : [ b ] ≡ t̂ (▷ γ a))
    --   → (kc : [ c ] ≡ t̂ (▷ (▷ γ a) b))
    --   → (▷ (σ γ a b) c)
    --   ≡ (▷ (▷ (▷ γ a) b) c)
    -- σπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    --   → (a : CT) (ka : [ a ] ≡ t̂ γ)
    --   → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ a))
    --   → (c : CT) (kc : [ c ] ≡ t̂ (▷ (▷ γ a) b))
    --   → π γ a (π (▷ γ a) b c)
    --   ≡ π γ (σ γ a b) c
    --   -- 
