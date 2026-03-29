module QIT.Prop where

open import QIT.Prop.Base public
open import QIT.Prop.Logic public

module ≡ where
  open import QIT.Prop.Path public
  open import QIT.Prop.Properties public
open ≡ public using (_≡_; subst; _≡ᵖ_; _≡ˢ_; ≡→≡ˢ; ≡ˢ→≡) public
