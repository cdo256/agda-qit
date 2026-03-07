module Automata.NFA where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Nullary 
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.Bool as Bool hiding (if_then_else_) renaming (_∨_ to _∨ᵇ_)
open import Data.Nat as Nat
open import QIT.Bool
open import Automata.Lang

record NFA (∑ : FinSet ℓ0) : Set₁ where
  field
    Q : Set

  ∑₀ = proj₁ ∑ 

  field
    δ : Q × ∑₀ → 𝒫 Q
    q₀ : Q
    F : Q → Bool

  record Config : Set₁ where
    constructor mkConfig
    field
      q* : 𝒫 Q
      w : List ∑₀

  initial : List ∑₀ → Config
  initial w = record
    { q* = [ q₀ ]
    ; w = w }

  step' : 𝒫 Q → ∑₀ → 𝒫 Q
  step' q* u = 
    (λ q → δ (q , u)) ⟨ q* ⟩

  step : Config → Config ⊎ Bool
  step cfg = case w of
    λ{ [] → inj₂ (foldr (λ q → F q ∨ᵇ_) false q*)
    ; (u ∷ w) → let q*' = step' q* u in
      inj₁ (mkConfig q*' w) }
    where
    open Config cfg

  simulate : (n : ℕ) → Config → Config ⊎ Bool
  simulate zero cfg = inj₁ cfg
  simulate (suc n) cfg with simulate n cfg
  ... | inj₁ cfg' = step cfg'
  ... | inj₂ b = inj₂ b

Accepts : {∑ : FinSet ℓ0} → ∑ *ᴸ → NFA ∑ → Prop₁
Accepts w nfa =
  ∃ λ n → simulate n (initial w) ≡p inj₂ true
  where
  open NFA nfa
  
accepts : {∑ : FinSet ℓ0} → ∑ *ᴸ → NFA ∑ → Bool
accepts w nfa = case simulate (length w) (initial w) of
  λ{(inj₂ true) → true
  ; _ → false }
  where
  open NFA nfa

DecidesLang : {∑ : FinSet ℓ0} → Lang ∑ → NFA ∑ → Prop₁
DecidesLang L nfa =
  ∀ w → L w ⇔ Accepts w nfa
