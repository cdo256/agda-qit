{-# OPTIONS --allow-unsolved-metas #-}
module QIT.Examples.ConTy.Tagged where

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
    t̂ : (γ : CT) (kγ : [ γ ] ≡ ĉ) → CT
    kt̂ : (γ : CT) (kγ : [ γ ] ≡ ĉ) → [ t̂ γ kγ ] ≡ k̂

    ∙ : CT
    k∙ : [ ∙ ] ≡ ĉ
    ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ) → CT
    k▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → [ ▷ γ kγ a ka ] ≡ ĉ
    u : (γ : CT) (kγ : [ γ ] ≡ ĉ) → CT
    ku : (γ : CT) (kγ : [ γ ] ≡ ĉ) → [ u γ kγ ] ≡ t̂ γ kγ 
    π : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (ka : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → CT
    kπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → [ π γ kγ a ka b kb ] ≡ t̂ γ kγ
    σ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (ka : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → CT
    kσ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → [ σ γ kγ a ka b kb ] ≡ t̂ γ kγ
    σ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → (c : CT) (kc : [ c ] ≡ t̂ (▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb)
                                 (k▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb))
      → (▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb)
      ≡ ▷ γ kγ (σ γ kγ a ka b kb) (kσ γ kγ a ka b kb)
    σπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → (c : CT) (kc : [ c ] ≡ t̂ (▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb)
                                 (k▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb))
      → π γ kγ a ka (π (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb c kc) (kπ (▷ γ _ a _) (k▷ γ kγ a ka) b kb c kc)
      ≡ π γ kγ (σ γ kγ a ka b kb) (kσ γ kγ a ka b kb) c
        (≡.trans kc (≡.dcongsp t̂ (σ▷ γ kγ a ka b kb (u (▷ (▷ γ _ a _) _ b _) _)
                                 (ku (▷ (▷ γ _ a _) _ b _) (k▷ (▷ γ _ a _) _ b _)))))
