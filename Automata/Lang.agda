module Automata.Lang where

open import QIT.Prelude hiding (if_then_else_)
open import QIT.Relation.Nullary 
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.Bool as Bool
open import Data.Nat as Nat

_*ᴸ : (∑ : FinSet ℓ0) → Set
∑ *ᴸ = List (proj₁ ∑)

Lang : (∑ : FinSet ℓ0) → Set₁
Lang ∑ = ∑ *ᴸ → Prop

tail? : ∀ {ℓA} {A : Set ℓA} → List A → List A
tail? [] = [] 
tail? (x ∷ xs) = xs

𝒫 : ∀ {ℓ} → Set ℓ → Set ℓ
𝒫 A = List A

_⟨_⟩ : ∀ {ℓA} {A : Set ℓA} → (A → 𝒫 A) → 𝒫 A → 𝒫 A
f ⟨ [] ⟩ = []
f ⟨ x ∷ xs ⟩ = f x ++ f ⟨ xs ⟩
