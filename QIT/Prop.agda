module QIT.Prop where

open import QIT.Prop.Base public
open import QIT.Logic
  renaming ( ∃i to ∣_,_∣ ; ∧i to _,_ ; ∧e₁ to fst ; ∧e₂ to snd
           ; ∨i₁ to inl ; ∨i₂ to inr
           ; ⊥e to absurdp') public
open import QIT.Prop.Data public

module ≡ where
  open import QIT.Identity public
  open import QIT.Prop.Properties public
open ≡ public using (_≡_; subst; _≡ᵖ_; _≡ˢ_; ≡→≡ˢ; ≡ˢ→≡) public
