module QIT.Nat where

open import QIT.Prelude
open import QIT.Prop
open import Data.Nat
open import Data.Nat.Properties

_≟ᴺ_ : Discrete ℕ
zero ≟ᴺ zero = yes ≡.refl
zero ≟ᴺ suc m = no λ ()
suc n ≟ᴺ zero = no λ ()
suc n ≟ᴺ suc m = case n ≟ᴺ m of
  λ{(no ¬p) → no λ q → ¬p (suc-injective q)
  ; (yes p) → yes (≡.cong suc p)}
