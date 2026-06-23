open import QIT.Prelude

module QIT.Prop ⦃ pathElim* : PathElim ⦄ where

open import QIT.Prop.Base public
open import QIT.Logic public
open import QIT.Prop.Data public

module ≡ where
  open import QIT.Identity public
  open import QIT.Prop.Properties public
open ≡ public using (_≡_; subst; _≡ˢ_; ≡→≡ˢ; ≡ˢ→≡) public
