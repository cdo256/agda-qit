module QIT.Mobile.Base (B : Set) where

open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)

data NodeType : Set where
  l : NodeType
  n : NodeType

open import Data.Unit
open import Data.Sum

Branch : Container ℓ0 ℓ0
Branch .Shape = NodeType
Branch .Position l = ⊥*
Branch .Position n = B

BTree = W Branch

leaf≡leaf : ∀ (f g : ⊥* → BTree) → sup (l , f) ≡ sup (l , g)
leaf≡leaf f g =
  ≡.cong (λ ○ → sup (l , ○)) (funExt λ ())

_∘ᵗ_ : ∀ (α : B → BTree) (π : B ↔ B)
     → B → BTree
(f ∘ᵗ π) = λ b → f (π .↔.to b)
