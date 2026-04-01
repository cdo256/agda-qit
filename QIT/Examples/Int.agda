module QIT.Examples.Int where

open import QIT.Prelude
open import QIT.Bool
open import QIT.Relation.Nullary
open import QIT.Prop hiding (_≡ˢ_)

postulate
  ℤ : Set
  z : ℤ
  s : ℤ → ℤ
  p : ℤ → ℤ
  sp : ∀ n → n ≡ s (p n)
  ps : ∀ n → n ≡ p (s n)

record ℤᴰ ℓ : Set (lsuc ℓ) where
  field
    Zᴰ : ℤ → Set ℓ
    zᴰ : Zᴰ z
    sᴰ : ∀ {n} → Zᴰ n → Zᴰ (s n)
    pᴰ : ∀ {n} → Zᴰ n → Zᴰ (p n)
    spᴰ : ∀ {n} → (x : Zᴰ n)
        → ≡.subst Zᴰ (sp n) x ≡ sᴰ (pᴰ x)
    psᴰ : ∀ {n} → (x : Zᴰ n)
        → ≡.subst Zᴰ (ps n) x ≡ pᴰ (sᴰ x)

record ℤˢ {ℓ} (A : ℤᴰ ℓ) : Set ℓ where
  open ℤᴰ A
  field
    Zˢ : ∀ n → Zᴰ n
    zˢ : Zˢ z ≡ zᴰ
    sˢ : ∀ {n} → Zˢ (s n) ≡ sᴰ (Zˢ n)
    pˢ : ∀ {n} → Zˢ (p n) ≡ pᴰ (Zˢ n)


record _≡ˢ_ {ℓ} {A : ℤᴰ ℓ} (e₁ e₂ : ℤˢ A) : Prop ℓ where
  module A = ℤᴰ A
  module e₁ = ℤˢ e₁
  module e₂ = ℤˢ e₂
  field
    Z≡ˢ : ∀ n → e₁.Zˢ n ≡ e₂.Zˢ n

postulate
  elim : ∀ {ℓ} (A : ℤᴰ ℓ) → ℤˢ A
  elim-unique
    : ∀ {ℓ} (A : ℤᴰ ℓ) (r : ℤˢ A)
    → r ≡ˢ elim A

module Examples where
  open import Data.Bool
  open ≡
  -1ℤ 0ℤ 1ℤ 2ℤ : ℤ
  -1ℤ = p z
  0ℤ = z
  1ℤ = s z
  2ℤ = s (s z)

  -_ : ℤ → ℤ
  -_ = Zˢ
    module - where
    A : ℤᴰ ℓ0
    A = record
      { Zᴰ = λ _ → ℤ
      ; zᴰ = z
      ; sᴰ = p
      ; pᴰ = s
      ; spᴰ = ps
      ; psᴰ = sp }  
    e : ℤˢ A
    e = elim A
    open ℤᴰ A public
    open ℤˢ e public
    
  isEven : ℤ → Bool
  isEven = Zˢ
    module isEven where
    A : ℤᴰ ℓ0
    A = record
      { Zᴰ = λ _ → Bool
      ; zᴰ = true
      ; sᴰ = not
      ; pᴰ = not
      ; spᴰ = λ b → sym (not-involutive b) 
      ; psᴰ = λ b → sym (not-involutive b) }  
    e : ℤˢ A
    e = elim A
    open ℤᴰ A public
    open ℤˢ e public

  isEven0ℤ : isEven 0ℤ ≡ true
  isEven0ℤ = isEven.zˢ
  ¬isEven1ℤ : isEven 1ℤ ≡ false
  ¬isEven1ℤ = trans isEven.sˢ
    (cong not isEven.zˢ)

  +2Even : ∀ n → isEven (s (s n)) ≡ isEven n
  +2Even n = begin
    isEven (s (s n))
      ≡⟨ isEven.sˢ ⟩
    not (isEven (s n))
      ≡⟨ cong not isEven.sˢ ⟩
    not (not (isEven n))
      ≡⟨ not-involutive _ ⟩
    isEven n ∎
    where
    open ≡.≡-Reasoning

  _+_ : ℤ → ℤ → ℤ
  m + n = Zˢ m
    module + where
    A : ℤᴰ ℓ0
    A = record
      { Zᴰ = λ _ → ℤ
      ; zᴰ = n
      ; sᴰ = s
      ; pᴰ = p
      ; spᴰ = sp
      ; psᴰ = ps }
    e : ℤˢ A
    e = elim A
    open ℤᴰ A public
    open ℤˢ e public

  even+even : ∀ m n
            → isEven m ≡ true
            → isEven n ≡ true
            → isEven (m + n) ≡ true
  even+even m n mEven nEven =
    ≡.trans (unbox (Zˢ m)) mEven
    where
    open ≡-Reasoning
    A : ℤᴰ ℓ0
    A = record
      { Zᴰ = λ m → Box (isEven (m + n) ≡ isEven m)
      ; zᴰ = box (
        isEven (z + n)
           ≡⟨ cong isEven (+.zˢ z n) ⟩
        isEven n
           ≡⟨ nEven ⟩
        true
           ≡⟨ sym isEven.zˢ ⟩
        isEven z ∎)
      ; sᴰ = λ {m} (box q) → box (
        isEven (s m + n)
           ≡⟨ cong isEven (+.sˢ m n) ⟩
        isEven (s (m + n))
           ≡⟨ isEven.sˢ ⟩
        not (isEven (m + n))
           ≡⟨ cong not q ⟩
        not (isEven m)
           ≡⟨ sym isEven.sˢ ⟩
        isEven (s m) ∎)
      ; pᴰ = λ {m} (box q) → box (
        isEven (p m + n)
           ≡⟨ cong isEven (+.pˢ m n) ⟩
        isEven (p (m + n))
           ≡⟨ isEven.pˢ ⟩
        not (isEven (m + n))
           ≡⟨ cong not q ⟩
        not (isEven m)
           ≡⟨ sym isEven.pˢ ⟩
        isEven (p m) ∎)
      ; spᴰ = λ _ → isPropBox _ _
      ; psᴰ = λ _ → isPropBox _ _ } 
    e : ℤˢ A
    e = elim A
    open ℤᴰ A public
    open ℤˢ e public
