module Scratch where

open import QW.Size renaming (_<_ to _≺_)
open import Prelude

absurd : {l l' : Level} {A : Set l} → ⊥ {l} → A
absurd ()

absurdp : {l l' : Level} {A : Prop l} → ⊥ {l} → A
absurdp ()

module NatSize where
  infix 4 _<_
  data _<_ : ℕ → ℕ → Prop where
    <zero : ∀ x → 0 < x +1
    <suc : ∀ x y → x < y → x +1 < y +1

  module _ {ℓ ℓ' : Level}{A : Set ℓ} {_≺_ : A → A → Prop ℓ'}
          {≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z} where

  data Trichotomy : ℕ → ℕ → Set where
    lt : ∀ {x y} → x < y → Trichotomy x y
    eq : ∀ {x y} → x == y → Trichotomy x y
    gt : ∀ {x y} → y < x → Trichotomy x y

  ¬le∧gt : ∀ {m n : ℕ} → m < n +1 → n < m → ⊥ {l = lzero} 
  ¬le∧gt {m +1} {n} (<suc m n m<n) n<sm = ¬le∧gt n<sm m<n

  _≟_ : (x y : ℕ) → Trichotomy x y
  zero ≟ zero = eq refl
  zero ≟ (y +1) = lt (<zero y)
  (x +1) ≟ zero = gt (<zero x)
  (x +1) ≟ (y +1) with x ≟ y
  ... | lt x<y = lt (<suc x y x<y)
  ... | eq x≡y = eq (ap suc x≡y)
  ... | gt x>y = gt (<suc y x x>y)

  iswf-rec : ∀ n → ∀ m → m < n → wf.Acc _<_ m
  iswf : wf.iswf _<_

  iswf-rec (n +1) m m<sn with m ≟ n
  ... | lt m<n = iswf-rec n m m<n
  ... | eq refl = wf.acc (iswf-rec n)
  ... | gt m>n = absurdp {l' = lzero} (¬le∧gt m<sn m>n)

  iswf n = wf.acc (iswf-rec n)

  max : ℕ → ℕ → ℕ
  max zero n = n
  max (m +1) zero = m +1
  max (m +1) (n +1) = (max m n) +1

  m<m+1 : ∀ m → m < m +1
  m<m+1 zero = <zero 0
  m<m+1 (m +1) = <suc m (m +1) (m<m+1 m)

  ℕˢ : SizeStructure ℕ
  ℕˢ ._≺_ = _<_
  ℕˢ .<< {zero} {j +1} {k +1} 0<sj sj<sk = <zero k
  ℕˢ .<< {i +1} {j +1} {k +1} (<suc j k i<j) (<suc i j j<k) =
    <suc i k (ℕˢ .<< i<j j<k)
  ℕˢ .<iswf = iswf
  ℕˢ .Oˢ = 0
  ℕˢ ._∨ˢ_ m n = (max m n) +1
  ℕˢ .<∨ˢl {zero} n = <zero n
  ℕˢ .<∨ˢl {m +1} zero = m<m+1 (m +1)
  ℕˢ .<∨ˢl {m +1} (n +1) = <suc m (max m n +1) (ℕˢ .<∨ˢl n)
  ℕˢ .<∨ˢr zero {n} = m<m+1 n
  ℕˢ .<∨ˢr (m +1) {zero} = <zero (m +1)
  ℕˢ .<∨ˢr (m +1) {n +1} = <suc n (max m n +1) (ℕˢ .<∨ˢr m)
