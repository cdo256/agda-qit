module QIT.Prelude where

open import QIT.Prelude.Universe public
open import QIT.Prelude.Truncation public
open import QIT.Prelude.Types renaming (⊥ˢ to ⊥; ⊥ˢ* to ⊥*) public
open import QIT.Prelude.Logic
  renaming ( ∃i to ∣_,_∣ ; ∧i to _,_ ; ∧e₁ to fst ; ∧e₂ to snd
           ; ∨i₁ to inl ; ∨i₂ to inr
           ; ⊥ to ⊥p ; ⊥* to ⊥p*) public
-- open import QIT.Prelude.Identity public
open import QIT.Prelude.HLevel public
open import QIT.Prelude.Axiom public
open import QIT.Prelude.Decidability public
