{-# OPTIONS --type-in-type #-}
module Mobile.Equivalence (B : Set) where

open import Prelude
open import Mobile.Base B
open import Equivalence
open import Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)

private
  l0 : Level
  l0 = lzero

data _≈ᵗ_ : BTree → BTree → Prop l0 where
  ≈leaf : ∀ {f g} → sup (l , f) ≈ᵗ sup (l , g)
  ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
        → sup (n , f) ≈ᵗ sup (n , g)
  ≈perm : ∀ {f} → (π : B ↔ B)
        → sup (n , f) ≈ᵗ sup (n , λ b → f (π .↔.to b))
  ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

≈refl : ∀ {t} → t ≈ᵗ t
≈refl {sup (l , f)} = ≈leaf
≈refl {sup (n , f)} = ≈node λ b → ≈refl {f b}

≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
≈sym ≈leaf = ≈leaf
≈sym (≈node c) = ≈node λ b → ≈sym (c b)
≈sym (≈perm {f} π) =
  substp A p x
  where
  module π = _↔_ π
  π' = ↔.flip π
  A : (B → B) → Prop l0
  A = λ h → sup (n , λ b → f (π.to b)) ≈ᵗ sup (n , λ b → f (h b))
  p : (λ b → π.to (π.from b)) ≡ (λ b → b)
  p = funExt λ b → π.linv b
  x : sup (n , λ b → f (π.to b)) ≈ᵗ sup (n , λ b → f (π.to (π.from b)))
  x = ≈perm {f = λ b → f (π.to b)} π'
≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

isEquiv-≈ᵗ : IsEquivalence _≈ᵗ_
isEquiv-≈ᵗ = record
  { refl = ≈refl
  ; sym = ≈sym
  ; trans = ≈trans }

MobileSetoid : Setoid l0 l0
MobileSetoid = record
  { Carrier = BTree
  ; _≈_ = _≈ᵗ_
  ; isEquivalence = isEquiv-≈ᵗ }

leaf≉node : ∀ {f g} → sup (l , g) ≈ᵗ sup (n , f) → ⊥p
leaf≉node (≈trans {t = sup (l , _)} p q) = leaf≉node q
leaf≉node (≈trans {t = sup (n , _)} p q) = leaf≉node p

l≢n : l ≡ n → ⊥p
l≢n ()
