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
ΣP≡' {a} {b} {A = A} {B = B} a1 a2 p = ≡.J C p λ b1 b2 → ≡.refl
  where
  C : ∀ a2 → a1 ≡ a2 → Set (a ⊔ b)
  C a2 p = ∀ (b1 : B a1) (b2 : B a2) → _≡_ {A = ΣP A B} (a1 , b1) (a2 , b2)

ΣP≡ : ∀ {a b} {A : Set a} {B : A → Prop b}
    → (x y : ΣP A B) → x .fst ≡ y .fst → x ≡ y
ΣP≡ x y p = ΣP≡' (x .fst) (y .fst) p (x .snd) (y .snd)

-- Logical existence on predicates.
∃ : ∀ {a b} {A : Set a} → (A → Prop b) → Prop (a ⊔ b)
∃ {A = A} B = ∥ ΣP A B ∥

substΣP : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Set ℓB} {a1 a2 : A} (p : a1 ≡ a2) (b : B a1) → Σ A B
substΣP {B = B} {a2 = a2} p b = a2 , subst B p b
