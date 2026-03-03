module Automata.DFA where

open import QIT.Prelude hiding (if_then_else_)
open import QIT.Relation.Nullary 
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.Bool as Bool

record DFA : Set₁ where
  field
    Q : Set
    ∑ : FinSet
    Γ : FinSet

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
      inj₁ (mkConfig q' (List.fromMaybe γ' ++ maybeTail γ) w) }
    where
    open Config cfg
    maybeTail : List Γ₀ → List Γ₀
    maybeTail [] = [] 
    maybeTail (x ∷ xs) = xs
