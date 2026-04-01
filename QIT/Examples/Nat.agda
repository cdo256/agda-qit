module QIT.Examples.Nat where

open import QIT.Prelude
open import QIT.Relation.Nullary
open import QIT.Prop hiding (_≡ˢ_)
open import Data.Bool.Properties 

postulate
  ℕ : Set
  z : ℕ
  s : ℕ → ℕ

record ℕᴰ ℓ : Set (lsuc ℓ) where
  field
    Nᴰ : ℕ → Set ℓ
    zᴰ : Nᴰ z
    sᴰ : ∀ {n} → Nᴰ n → Nᴰ (s n)

record ℕˢ {ℓ} (A : ℕᴰ ℓ) : Set ℓ where
  open ℕᴰ A
  field
    Nˢ : ∀ n → Nᴰ n
    zˢ : Nˢ z ≡ zᴰ
    sˢ : ∀ {n} → Nˢ (s n) ≡ sᴰ (Nˢ n)


record _≡ˢ_ {ℓ} {A : ℕᴰ ℓ} (e₁ e₂ : ℕˢ A) : Prop ℓ where
  module A = ℕᴰ A
  module e₁ = ℕˢ e₁
  module e₂ = ℕˢ e₂
  field
    N≡ˢ : ∀ n → e₁.Nˢ n ≡ e₂.Nˢ n

postulate
  elim : ∀ {ℓ} (A : ℕᴰ ℓ) → ℕˢ A
  elim-unique
    : ∀ {ℓ} (A : ℕᴰ ℓ) (r : ℕˢ A)
    → r ≡ˢ elim A

module Examples where
  open import Data.Bool
  0ℕ : ℕ
  0ℕ = z
  1ℕ : ℕ
  1ℕ = s z
  2ℕ : ℕ
  2ℕ = s (s z)

  isEven : ℕ → Bool
  isEven = Nˢ
    module isEven where
    A : ℕᴰ ℓ0
    A = record
      { Nᴰ = λ _ → Bool
      ; zᴰ = true
      ; sᴰ = not }
    e : ℕˢ A
    e = elim A
    open ℕˢ e public

  isEven0 : isEven z ≡ true
  isEven0 = isEven.zˢ

  ¬isEven1 : isEven 1ℕ ≡ false
  ¬isEven1 = ≡.trans isEven.sˢ (≡.cong not isEven0)

  isEven2 : isEven 2ℕ ≡ true
  isEven2 =
    ≡.trans
      isEven.sˢ
      (≡.cong not ¬isEven1)

  +2Even : ∀ n → isEven (s (s n)) ≡ isEven n
  +2Even n = begin
    isEven (s (s n))
      ≡⟨ isEven.sˢ ⟩
    not (isEven (s n))
      ≡⟨ ≡.cong not isEven.sˢ ⟩
    not (not (isEven n))
      ≡⟨ ≡ˢ→≡ (not-involutive _) ⟩
    isEven n ∎
    where
    open ≡.≡-Reasoning

  _+_ : ℕ → ℕ → ℕ
  m + n = Nˢ m
    module + where
    A : ℕᴰ ℓ0
    A = record
      { Nᴰ = λ _ → ℕ
      ; zᴰ = n
      ; sᴰ = s }
    e : ℕˢ A
    e = elim A
    open ℕˢ e public

  even+even : ∀ m n
            → isEven m ≡ true
            → isEven n ≡ true
            → isEven (m + n) ≡ true
  even+even m n mEven nEven =
    ≡.trans (unbox (Nˢ m)) mEven
    where
    A : ℕᴰ ℓ0
    A = record
      { Nᴰ = λ m → Box (isEven (m + n) ≡ isEven m)
      ; zᴰ = box (≡.trans
        (≡.cong isEven (+.zˢ z n))
        (≡.trans nEven (≡.sym isEven.zˢ)))
      ; sᴰ = λ (box p)
           → box (≡.trans
               (≡.cong isEven (+.sˢ m n))
               (≡.trans
                 isEven.sˢ
                 (≡.trans
                   (≡.cong not p)
                   (≡.sym isEven.sˢ)))) }
    e : ℕˢ A
    e = elim A
    open ℕˢ e public
