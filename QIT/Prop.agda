module QIT.Prop where

open import QIT.Prop.Base public
open import QIT.Prop.Logic public
open import QIT.Prop.Data public
open import QIT.Prop.SetPath public
  using (_≡ˢ_; reflˢ; congˢ; substˢ; Jˢ; funExtˢ; symˢ; transˢ; subst-idˢ; subst-constˢ; cong₂ˢ; subst₂ˢ; dcongˢ; dcong₂ˢ; subst-substˢ; subst-invˢ; Σ≡ˢ; funExtˢ⁻; ≡→≡ˢ; ≡ˢ→≡)
import QIT.Prop.SetPath as ≡ˢ
module ≡ˢ-Reasoning = ≡ˢ.≡ˢ-Reasoning

module ≡ where
  open import QIT.Prop.Path public
  open import QIT.Prop.Properties public
open ≡ public using (_≡_; subst; _≡ᵖ_) public
