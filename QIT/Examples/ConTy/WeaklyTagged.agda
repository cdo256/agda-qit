{-# OPTIONS --allow-unsolved-metas #-}
module QIT.Examples.ConTy.WeaklyTagged where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

record Algebra : Set₁ where
  field
    CT : Set
    [_] : CT → CT
    k̂ : CT
    kk̂ : [ k̂ ] ≡ k̂
    ĉ : CT
    kĉ : [ ĉ ] ≡ k̂
    t̂ : (γ : CT) → CT
    kt̂ : (γ : CT) (kγ : [ γ ] ≡ ĉ) → [ t̂ γ ] ≡ k̂

    ∙ : CT
    k∙ : [ ∙ ] ≡ ĉ
    ▷ : (γ : CT) (a : CT) → CT
    k▷ : (γ : CT) (a : CT)
      → (kγ : [ γ ] ≡ ĉ)
      → (ka : [ a ] ≡ t̂ γ)
      → [ ▷ γ a ] ≡ ĉ
    u : (γ : CT) → CT
    ku : (γ : CT)
      → (kγ : [ γ ] ≡ ĉ)
      → [ u γ ] ≡ t̂ γ 
    π : (γ : CT) (a : CT) (b : CT) → CT
    kπ : (γ : CT) (a : CT) (b : CT) 
      → (kγ : [ γ ] ≡ ĉ)
      → (ka : [ a ] ≡ t̂ γ)
      → (kb : [ b ] ≡ t̂ (▷ γ a))
      → [ π γ a b ] ≡ t̂ γ 
    σ : (γ : CT) (a : CT) (b : CT) → CT
    kσ : (γ : CT) (a : CT) (b : CT) 
      → (kγ : [ γ ] ≡ ĉ)
      → (ka : [ a ] ≡ t̂ γ)
      → (kb : [ b ] ≡ t̂ (▷ γ a))
      → [ σ γ a b ] ≡ t̂ γ 
    σ▷ : (γ : CT) (a : CT) (b : CT) (c : CT) 
      → (kγ : [ γ ] ≡ ĉ)
      → (ka : [ a ] ≡ t̂ γ)
      → (kb : [ b ] ≡ t̂ (▷ γ a))
      → (kc : [ c ] ≡ t̂ (▷ (▷ γ a) b))
      → (▷ (σ γ a b) c)
      ≡ (▷ (▷ (▷ γ a) b) c)
    σπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ a))
      → (c : CT) (kc : [ c ] ≡ t̂ (▷ (▷ γ a) b))
      → π γ a (π (▷ γ a) b c)
      ≡ π γ (σ γ a b) c
