module QIT.Subset where

open import QIT.Prelude
open import Data.Product

record ΣP {a b} (A : Set a) (B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open ΣP public

infixr 4 _,_

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
