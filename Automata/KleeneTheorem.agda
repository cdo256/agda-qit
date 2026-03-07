module Automata.KleeneTheorem where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Nullary 
open import QIT.Relation.Subset 
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.Bool as Bool hiding (if_then_else_) renaming (_∨_ to _∨ᵇ_)
open import Data.Nat as Nat
open import QIT.Bool
open import Automata.Lang
import Automata.DFA as DFA
import Automata.NFA as NFA
open DFA using (DFA)
open NFA using (NFA)

module _ {∑ : FinSet ℓ0} where
  DFA→NFA : DFA ∑ → NFA ∑
  DFA→NFA M = record
    { Q = Q
    ; δ = λ (q , u) → [ δ (q , u) ]
    ; q₀ = q₀
    ; F = F }
    where
    open DFA.DFA M

  record _~_ {M : DFA ∑} (cfgM : DFA.Config M) (cfgN : NFA.Config (DFA→NFA M)) : Set₁ where
    module M = DFA.DFA M
    module cfgM = DFA.Config cfgM
    module cfgN = NFA.Config cfgN
    field
      q-eq : cfgN.q* ≡ [ cfgM.q ]
      w-eq : cfgN.w ≡ cfgM.w

  -- Bisimulates : DFA ∑ → NFA ∑ → Set₁
  -- Bisimulates M N = {!∀ w → !}
  --   where
  --   module M = DFA.DFA M
  --   module N = NFA.NFA N

  -- -- Theorem : Prop _
  -- -- Theorem = ∃ (DFA.DecidesLang L)
  -- --         ⇔ ∃ (NFA.DecidesLang L)
  -- -- theorem : Theorem
  -- -- theorem = dfa→nfa , nfa→dfa
  -- --   where
  -- --   dfa→nfa : ∃ (DFA.DecidesLang L)
  -- --           → ∃ (NFA.DecidesLang L)
  -- --   dfa→nfa ∣ dfa , dec ∣ = ∣ nfa , dec' ∣
  -- --     where
  -- --     open DFA.DFA dfa
  -- --     nfa : NFA ∑
  -- --     nfa = record
  -- --       { Q = Q
  -- --       ; δ = λ (q , u) → [ δ (q , u) ]
  -- --       ; q₀ = q₀
  -- --       ; F = F }
  -- --     dec' : NFA.DecidesLang L nfa
  -- --     dec' w = (λ x → ∣ length w , {!!} ∣) , {!!}
        
  -- --   nfa→dfa : ∃ (NFA.DecidesLang L)
  -- --           → ∃ (DFA.DecidesLang L)
  -- --   nfa→dfa = {!!}
    
