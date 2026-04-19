module QIT.Examples.F where

open import QIT.Prelude
open import Data.Nat
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Set.Base
open import QIT.Function.Base

recℕ : ∀ {X : Set} → X → (X → X) → ℕ → X
recℕ z s zero = z
recℕ z s (suc n) = s (recℕ z s n)

postulate
  F : Set
  z : F
  s : F → F
  sup : (ℕ → F) → F

_∪_ : ∀ {X : Set} → (ℕ → X) → (ℕ → X) → (ℕ → X)
(f ∪ g) zero = f 0
(f ∪ g) (suc n) = (g ∪ (f ∘ suc)) n

[_] : ∀ {X : Set} → X → ℕ → X
[ x ] _ = x

postulate
  pair : (ℕ × ℕ) ↔ ℕ

module pair = _↔_ pair

_∈_ : {X : Set} → X → (ℕ → X) → Prop
x ∈ f = ∃ λ i → f i ≡ x

_⊆_ : {X Y Z : Set} → (X → Z) → (Y → Z) → Prop
f ⊆ g = ∀ x → ∃ λ y → f x ≡ g y 

postulate
  p1 : (f g : ℕ → ℕ)
     → (∀ n → (n ∈ f) ⇔ (n ∈ g))
     → (h : ℕ → F)
     → sup (h ∘ f) ≡ sup (h ∘ g)

  p2 : (f g : ℕ → F)
     → sup (f ∪ [ sup (f ∪ g) ]) ≡ sup (f ∪ g)

  p3 : (f g : ℕ → F)
     → sup (f ∪ [ s (sup (f ∪ g)) ])
     ≡ s (sup (f ∪ g))

  p4 : (b c : ℕ → ℕ)
     → Surjective (b ∪ c) -- jointly surjective
     → (L : ℕ → ℕ → ℕ)
     → (∀ n → ∃ λ m → c n ∈ L (b m))
     → (∀ n → ∃ λ m → b n ∈ L (c m))
     → (h : ℕ → F)
     → let k : ℕ → ℕ → F
           k = recℕ h λ h n → sup (h ∘ L n)
           f : ℕ → ℕ → F 
           f j = k j ∘ b
           g : ℕ → ℕ → F 
           g j = k j ∘ c
           ḟ : ℕ → F
           ḟ jn = let (j , n) = pair.from jn in f j n
           ġ : ℕ → F
           ġ jn = let (j , n) = pair.from jn in g j n
       in sup ḟ ≡ sup ġ

  p5 : sup [ z ] ≡ z
