open import QIT.Prelude

module QIT.Prop where

open import QIT.Logic public

module ≡ where
  open import QIT.Identity public
open ≡ public using (_≡_; subst; _≡ˢ_; ≡→≡ˢ; ≡ˢ→≡) public
