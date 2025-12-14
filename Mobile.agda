module Mobile where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product
open import Function.Bundles
open import Function.Definitions
open import Relation.Binary.PropositionalEquality as ≡
open import Axiom
open import Setoid as S
open import Function.Properties.Inverse 

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

data BTree (B : Set ℓ) : Set ℓ where
  leaf : BTree B
  node : (f : B → BTree B) → BTree B

module Mobile (B : Set ℓ) where
  Bˢ : Setoid ℓ ℓ
  Bˢ = setoid B
  open Inverse renaming (inverse to inverse')
  data _≈ᵗ_ : BTree B → BTree B → Set ℓ where
    ≈leaf : leaf ≈ᵗ leaf
    ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
          → node f ≈ᵗ node g
    ≈perm : ∀ {f} → (π : B ↔ B)
          → node f ≈ᵗ node λ b → f (π .to b)
    ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

  ≈refl : ∀ {t} → t ≈ᵗ t
  ≈refl {leaf} = ≈leaf
  ≈refl {node f} = ≈node λ b → ≈refl {f b}

  ≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
  ≈sym (≈perm {f} π) =
    subst
      (λ h → node (λ b → f (π .to b)) ≈ᵗ node λ b → f (h b))
      (funExt λ b → π .inverse' .proj₁ ≡.refl)
      (≈perm {f = λ b → f (π .to b)} (↔-sym π))
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  MobileSetoid : Setoid {!!} {!!}
  MobileSetoid = record
    { Carrier = BTree B
    ; _≈_ = _≈ᵗ_
    ; isEquivalence = record
      { refl = ≈refl
      ; sym = ≈sym
      ; trans = ≈trans } }
