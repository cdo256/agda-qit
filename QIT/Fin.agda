module QIT.Fin where

open import QIT.Prelude
open import QIT.Prop
open import Data.Fin
open import Data.Fin.Properties

_≟ꟳ_ : ∀ {n} → Discrete (Fin n) 
zero ≟ꟳ zero = yes ≡.refl
zero ≟ꟳ suc j = no (λ ())
suc i ≟ꟳ zero = no (λ ())
suc i ≟ꟳ suc j = case i ≟ꟳ j of
  λ{(no ¬p) → no (λ q → ¬p (suc-injective q))
  ; (yes p) → yes (≡.cong suc p) }

