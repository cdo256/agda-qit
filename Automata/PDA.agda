module Automata.PDA where

open import QIT.Prelude hiding (if_then_else_)
open import QIT.Relation.Nullary 
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.Bool as Bool
open import Data.Nat as Nat
open import Automata.Lang

record DFA (∑ : FinSet ℓ0) : Set₁ where
  field
    Q : Set
    Γ : FinSet ℓ0

  Γ₀ = proj₁ Γ
  ∑₀ = proj₁ ∑ 
  Γₑ = Maybe Γ₀

  field
    δ : Q × ∑₀ × Γₑ → Q × Γₑ
    q₀ : Q
    F : Q → Bool

  -- module _ (dfa : DFA) where
  --   open DFA dfa 

  record Config : Set₁ where
    constructor mkConfig
    field
      q : Q
      γ : List Γ₀
      w : List ∑₀

  initial : List ∑₀ → Config
  initial w = record
    { q = q₀
    ; γ = []
    ; w = w }

  step : Config → Config ⊎ Bool
  step cfg = case w of
    λ{ [] → if F q then inj₂ true else inj₂ false
    ; (u ∷ w) → let (q' , γ') = δ (q , u , head γ) in
      inj₁ (mkConfig q' (γ' ?∷ tail? γ) w) }
    where
    open Config cfg

  simulate : (n : ℕ) → Config → Config ⊎ Bool
  simulate zero cfg = inj₁ cfg
  simulate (suc n) cfg with simulate n cfg
  ... | inj₁ cfg' = step cfg'
  ... | inj₂ b = inj₂ b

Accepts? : {∑ : FinSet ℓ0} → DFA ∑ → Lang ∑ → Set₁
Accepts? dfa w = Σ ℕ λ n → simulate n (initial w) ≡ inj₂ true
  where
  open DFA dfa

accepts : {∑ : FinSet ℓ0} → DFA ∑ → Lang ∑ → Bool
accepts dfa w = case simulate (length w) (initial w) of
  λ{(inj₂ true) → true
  ; _ → false }
  where
  open DFA dfa

isRegular : {∑ : FinSet ℓ0} → Lang ∑ → Set₁
isRegular {∑} w = Σ (DFA ∑) λ dfa → Accepts? dfa w
