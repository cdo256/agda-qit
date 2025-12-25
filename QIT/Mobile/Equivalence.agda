{-# OPTIONS --type-in-type #-}
module QIT.Mobile.Equivalence (B : Set) where

open import QIT.Prelude
open import QIT.Mobile.Base B
open import QIT.Equivalence
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)

private
  l0 : Level
  l0 = lzero

module _ (S : Setoid l0 l0) where
  module S = Setoid S
  F̃-ob₀ : Set
  F̃-ob₀ = ⟦ Branch ⟧ ⟨ S ⟩
  data _≈ᵗ_ : F̃-ob₀ → F̃-ob₀ → Prop l0 where
    ≈leaf : ∀ {f g} → (l , f) ≈ᵗ (l , g)
    ≈node : ∀ {f g} → (c : ∀ b → f b S.≈ g b)
          → (n , f) ≈ᵗ (n , g)
    ≈perm : ∀ {f} → (π : B ↔ B)
          → (n , f) ≈ᵗ (n , λ b → f (π .↔.to b))
    ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

  ≈refl : ∀ {t} → t ≈ᵗ t
  ≈refl {(l , f)} = ≈leaf
  ≈refl {(n , f)} = ≈node λ b → S.refl

  ≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → S.sym (c b)
  ≈sym (≈perm {f} π) =
    substp A p q
    where
    module π = _↔_ π
    π' = ↔.flip π
    A : (B → B) → Prop l0
    A = λ h → (n , λ b → f (π.to b)) ≈ᵗ (n , λ b → f (h b))
    p : (λ b → π.to (π.from b)) ≡ (λ b → b)
    p = funExt λ b → π.linv b
    q : (n , λ b → f (π.to b)) ≈ᵗ (n , λ b → f (π.to (π.from b)))
    q = ≈perm {f = λ b → f (π.to b)} π'
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  isEquiv-≈ᵗ : IsEquivalence _≈ᵗ_
  isEquiv-≈ᵗ = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans }

  F̃-ob : Setoid l0 l0
  F̃-ob = record
    { Carrier = F̃-ob₀
    ; _≈_ = _≈ᵗ_
    ; isEquivalence = isEquiv-≈ᵗ }

  leaf≉node : ∀ {f g} → (l , g) ≈ᵗ (n , f) → ⊥p
  leaf≉node (≈trans {t = (l , _)} p q) = leaf≉node q
  leaf≉node (≈trans {t = (n , _)} p q) = leaf≉node p

  l≢n : l ≡ n → ⊥p
  l≢n ()
