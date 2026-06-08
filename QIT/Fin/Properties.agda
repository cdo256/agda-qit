module QIT.Fin.Properties where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import Data.Fin as Fin hiding (_≟_; pred) public
open import Data.Nat hiding (_≟_) renaming (_>_ to _>ᴺ_)

ℕ-suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
ℕ-suc-injective = ≡.cong pred

Fin-suc-injective : ∀ {m} {a : Fin m} {b : Fin m}
                  → suc a ≡ suc b → a ≡ b
Fin-suc-injective ≡.refl = ≡.refl

_≟ℕ_ : Discrete ℕ
zero ≟ℕ zero = yes ≡.refl
zero ≟ℕ suc m = no λ ()
suc n ≟ℕ zero = no λ ()
suc n ≟ℕ suc m = case n ≟ℕ m of
  λ{(no ¬p) → no λ q → ¬p (ℕ-suc-injective q)
  ; (yes p) → yes (≡.cong suc p)}

_≟Fin_ : ∀ {n} → Discrete (Fin n) 
zero ≟Fin zero = yes ≡.refl
zero ≟Fin suc j = no (λ ())
suc i ≟Fin zero = no (λ ())
suc i ≟Fin suc j = case i ≟Fin j of
  λ{(no ¬p) → no λ q → ¬p (Fin-suc-injective q)
  ; (yes p) → yes (≡.cong suc p) }

inhab⇔>0 : ∀ {n} → ∥ Fin n ∥ ⇔ ∥ n >ᴺ 0 ∥
inhab⇔>0 {zero} = p , q
  where
  p : ∥ Fin zero ∥ → ∥ zero >ᴺ 0 ∥
  p ∣ () ∣
  q : ∥ zero >ᴺ 0 ∥ → ∥ Fin zero ∥
  q ∣ () ∣
inhab⇔>0 {suc n} = p , q
  where
  p : ∥ Fin (suc n) ∥ → ∥ suc n >ᴺ 0 ∥
  p _ = ∣ s≤s z≤n ∣
  q : ∥ suc n >ᴺ 0 ∥ → ∥ Fin (suc n) ∥
  q = λ _ → ∣ zero ∣

↔to⇔ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → A ↔ B → ∥ A ∥ ⇔ ∥ B ∥
↔to⇔ {A = A} {B} p = q₁ , q₂
  where
  open _↔_ p
  q₁ : ∥ A ∥ → ∥ B ∥
  q₁ ∣ x ∣ = ∣ to x ∣
  q₂ : ∥ B ∥ → ∥ A ∥
  q₂ ∣ x ∣ = ∣ from x ∣

Fin↔-injective : ∀ {m n} → Fin m ↔ Fin n → m ≡ n
Fin↔-injective {m} {n} p = {!!}
  where
  open _↔_ p
  m>0⇔n>0 : ∥ m >ᴺ 0 ∥ ⇔ ∥ n >ᴺ 0 ∥
  m>0⇔n>0 = ⇔trans (⇔sym inhab⇔>0) (⇔trans (↔to⇔ p) inhab⇔>0)
  descend : Dec (m >ᴺ 0) → m ≡ n
  descend (yes (s≤s z≤n)) = {!!}
  descend (no ¬p) = {!!}

¬Fin0 : ¬ ∥ Fin 0 ∥
¬Fin0 ∣ () ∣

fzero≠fsuc : ∀ {n} (a : Fin n) → zero ≢ suc a
fzero≠fsuc a ()

Fin↔-suc : ∀ {m n} → Fin (suc m) ↔ Fin (suc n) → Fin m ↔ Fin n
Fin↔-suc {m} {n} p = {!!}
  where
  f' : ∀ {m n} → (p : Fin (suc m) ↔ Fin (suc n)) → (a : Fin m) → Singleton (p .↔.to (suc a)) → Singleton (p .↔.to zero) → Fin n
  f' p a (zero , q) (zero , r) =
    absurdp (fzero≠fsuc a (≡.trans (≡.sym (p.rinv zero))
                           (≡.trans (≡.cong p.from (≡.trans (≡.sym r) q))
                            (p.rinv (suc a)))))
    where module p = _↔_ p
  f' p a (zero , _) (suc c , _) = c
  f' p a (suc b , _) _ = b

  f : ∀ {m n} → (p : Fin (suc m) ↔ Fin (suc n)) → (a : Fin m) → Fin n
  f p a = f' p a (inspect (p .↔.to (suc a))) (inspect (p .↔.to zero))
    where module p = _↔_ p

  module p = _↔_ p
  q : Fin m ↔ Fin n
  q = record
    { to = to
    ; from = from
    ; rinv = rinv
    ; linv = linv }
    where
    to : Fin m → Fin n
    to = f p
    from : Fin n → Fin m
    from = f (↔.flip p)
    linv : (a : Fin n) → to (from a) ≡ a
    linv a with inspect (p.from (suc a)) | inspect (p.from zero)
    ... | zero , q | zero , r = absurdp' {!!}
    ... | zero , q | suc u , r = {!!}
    ... | suc b , q | v , r = {!!}
    rinv : (a : Fin m) → from (to a) ≡ a

-- Fin↔-injective' : ∀ {m n} → Fin m ↔ Fin n → m ≡ n
-- Fin↔-injective' {zero} {zero} p = ≡.refl
-- Fin↔-injective' {zero} {suc n} p = absurdp' (¬Fin0 ∣ from zero ∣)
--   where open _↔_ p
-- Fin↔-injective' {suc m} {zero} p = absurdp' (¬Fin0 ∣ to zero ∣)
--   where open _↔_ p
-- Fin↔-injective' {suc m} {suc n} p
--   with p .↔.to zero ≟Fin zero
-- ... | yes r = ≡.cong suc (Fin↔-injective' q)
--   where
--   module p = _↔_ p
--   q : Fin m ↔ Fin n
--   q = record
--     { to = to
--     ; from = {!!}
--     ; rinv = {!!}
--     ; linv = {!!} }
--     where
--     to : Fin m → Fin n
--     to a with inspect (p.to (suc a))
--     ... | zero , u = absurdp (fzero≠fsuc a (≡.trans (≡.sym (p.rinv zero)) (≡.trans (≡.cong p.from (≡.trans r u)) (p.rinv (suc a)))))
--     ... | suc b , _ = b
-- ... | no ¬r = ≡.cong suc {!Fin↔-injective' q!}
  
