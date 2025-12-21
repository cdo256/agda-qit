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

Bˢ : Setoid l0 l0
Bˢ = ≡setoid B
data _≈ᵗ_ : BTree → BTree → Prop l0 where
  ≈leaf : ∀ {f g} → leaf {f} ≈ᵗ leaf {g}
  ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
        → node f ≈ᵗ node g
  ≈perm : ∀ {f} → (π : ≈.Iso Bˢ Bˢ)
        → node f ≈ᵗ node λ b → f (≈.Iso.⟦_⟧ π b)
  ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

≈refl : ∀ {t} → t ≈ᵗ t
≈refl {leaf} = ≈leaf
≈refl {node f} = ≈node λ b → ≈refl {f b}

≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
≈sym ≈leaf = ≈leaf
≈sym (≈node c) = ≈node λ b → ≈sym (c b)
≈sym (≈perm {f} π) =
  substp' A p x
  where
  module π = ≈.Iso π
  π' = ≈.IsoFlip π
  A : (B → B) → Prop l0
  A = λ h → node (λ b → f π.⟦ b ⟧) ≈ᵗ node λ b → f (h b)
  p : (λ b → π.⟦ π.⟦ b ⟧⁻¹ ⟧) ≡p (λ b → b)
  p = funExtp λ b → (π.linv b)
  x : node (λ b → f π.⟦ b ⟧) ≈ᵗ node (λ b → f π.⟦ π.⟦ b ⟧⁻¹ ⟧)
  x = ≈perm {f = λ b → f π.⟦ b ⟧} π'
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

leaf≉node : ∀ {f g} → leaf {g} ≈ᵗ node f → ⊥p
leaf≉node (≈trans {t = leaf} p q) = leaf≉node q
leaf≉node (≈trans {t = node _} p q) = leaf≉node p

l≢n : l ≡ n → ⊥p
l≢n ()
