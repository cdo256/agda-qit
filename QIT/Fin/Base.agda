module QIT.Fin.Base where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Function.Base 
open import Data.Fin as Fin hiding (_≟_) public
open import Data.Fin.Properties using (suc-injective) 
open import Data.Nat hiding (_≟_)
open import Data.Nat.Properties using () renaming (suc-injective to ℕ-suc-injective)
open import QIT.Relation.Nullary 

_≟ℕ_ : Discrete ℕ
zero ≟ℕ zero = yes (box ≡.refl)
zero ≟ℕ suc m = no λ ()
suc n ≟ℕ zero = no λ ()
suc n ≟ℕ suc m = case n ≟ℕ m of
  λ{(no ¬p) → no λ (box q) → ¬p (box {!ℕ-suc-injective {!q!}!})
  ; (yes p) → {!yes (≡.cong suc p)!}}

-- _≟Fin_ : ∀ {n} → Discrete (Fin n) 
-- zero ≟Fin zero = yes ≡.refl
-- zero ≟Fin suc j = no (λ ())
-- suc i ≟Fin zero = no (λ ())
-- suc i ≟Fin suc j = case i ≟Fin j of
--   λ{(no ¬p) → no (λ q → ¬p (suc-injective q))
--   ; (yes p) → yes (≡.cong suc p) }
