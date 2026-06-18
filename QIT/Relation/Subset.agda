module QIT.Relation.Subset where

open import QIT.Prelude
open import QIT.Prop

-- Refinement type of A under B
-- This defines a particular subset of A. It is the same definition as
-- for standard Σ types, except the second component is a predicate
-- rather than type family (Prop instead of Set).
record ΣP {a b} (A : Set a) (B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open ΣP public

infixr 4 _,_

⟨_⟩ᴾ : ∀ {a b} {A : Set a} {B : A → Prop b} → ΣP A B → A
⟨ x , _ ⟩ᴾ = x

-- Two variants on cubical's Σ≡Prop in a standard Agda environment.
ΣP≡' : ∀ {a b} {A : Set a} {B : A → Prop b}
    → (a1 a2 : A) → a1 ≡ a2
    → ∀ (b1 : B a1) (b2 : B a2) → _≡_ {A = ΣP A B} (a1 , b1) (a2 , b2)
ΣP≡' {a} {b} {A = A} {B = B} a1 a2 p = ≡.Jp C p λ b1 b2 → ≡.refl
  where
  C : ∀ a2 → a1 ≡ a2 → Prop (a ⊔ b)
  C a2 p = ∀ (b1 : B a1) (b2 : B a2) → _≡_ {A = ΣP A B} (a1 , b1) (a2 , b2)

ΣP≡ : ∀ {a b} {A : Set a} {B : A → Prop b}
    → (x y : ΣP A B) → x .fst ≡ y .fst → x ≡ y
ΣP≡ x y p = ΣP≡' (x .fst) (y .fst) p (x .snd) (y .snd)

-- Logical existence on predicates.
∃ : ∀ {a b} {A : Set a} → (A → Prop b) → Prop (a ⊔ b)
∃ {A = A} B = ∥ ΣP A B ∥

-- Logical existence on predicates.
∃' : ∀ {a b} {A : Set a} → (A → Set b) → Prop (a ⊔ b)
∃' {A = A} B = ∥ Σ A B ∥

substΣP : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {a1 a2 : A} (p : a1 ≡ a2) (b : B a1) → Σ A B
substΣP {B = B} {a2 = a2} p b = a2 , subst B p b

Singleton : ∀ {ℓA} {A : Set ℓA} (a : A) → Set ℓA
Singleton {A = A} a = ΣP A (_≡ a)

inspect : ∀ {ℓA} {A : Set ℓA} (x : A) → Singleton x
inspect x = x , ≡.refl

𝓟 : ∀ {ℓ𝓤} ℓ𝓟 → (𝓤 : Set ℓ𝓤) → Set (ℓ𝓤 ⊔ lsuc ℓ𝓟)
𝓟 ℓ𝓟  𝓤 = 𝓤 → Prop ℓ𝓟

module Subset {ℓ𝓤} ℓ𝓟 (𝓤 : Set ℓ𝓤) where
  𝓟𝓤 = 𝓟 ℓ𝓟 𝓤
  open import Data.List

  infix 30 _∈_
  infix 40 _∪_ _∩_
  _∈_ : (x : 𝓤) (X : 𝓟𝓤) → Prop ℓ𝓟
  x ∈ X = X x

  ∅ : 𝓟𝓤
  ∅ _ = ⊥p*

  𝓤̇ : 𝓟𝓤
  𝓤̇ _ = ⊤p*

  [_]ᴾ : List 𝓤 → 𝓟 (ℓ𝓤 ⊔ ℓ𝓟) 𝓤
  [ [] ]ᴾ _ = ⊥p*
  [ x ∷ xs ]ᴾ y = (x ≡ y) ∨ ([ xs ]ᴾ y)

  _∪_ : 𝓟𝓤 → 𝓟𝓤 → 𝓟𝓤
  (X ∪ Y) x = x ∈ X ∨ x ∈ Y

  _∩_ : 𝓟𝓤 → 𝓟𝓤 → 𝓟𝓤
  (X ∩ Y) x = x ∈ X ∧ x ∈ Y

  ⋃ : ∀ {ℓI} (I : Set ℓI) → (I → 𝓟𝓤) → 𝓟 (ℓ𝓟 ⊔ ℓI) 𝓤
  ⋃ I X x = ∃ λ i → x ∈ X i

  ⋂ : ∀ {ℓI} (I : Set ℓI) → (I → 𝓟𝓤) → 𝓟 (ℓ𝓟 ⊔ ℓI) 𝓤
  ⋂ I X x = ∀ i → x ∈ X i

  record _↔ₛ_ (X Y : 𝓟𝓤) : Set (ℓ𝓟 ⊔ ℓ𝓤) where
    field
      to   : ∀ x → X x → Y x
      from : ∀ x → Y x → X x
