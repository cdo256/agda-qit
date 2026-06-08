module QIT.Fin.Properties where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
open import Data.Fin as Fin hiding (_≟_; pred) public
open import Data.Nat as ℕ hiding (_≟_) renaming (_>_ to _>ᴺ_)

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

¬Fin0 : ¬ ∥ Fin 0 ∥
¬Fin0 ∣ () ∣

fzero≠fsuc : ∀ {n} (a : Fin n) → zero ≢ suc a
fzero≠fsuc a ()

Fin↔-suc : ∀ {m n} → Fin (suc m) ↔ Fin (suc n) → Fin m ↔ Fin n
Fin↔-suc {m} {n} p = q
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
    ... | zero , q | zero , r = absurdp' (fzero≠fsuc a eq)
      where
      eq : zero ≡ suc a
      eq = ≡.trans (≡.sym (≡.trans (≡.cong p.to r) (p.linv zero)))
                    (≡.trans (≡.cong p.to q) (p.linv (suc a)))
    ... | zero , q | suc u , r with inspect (p.to (suc u)) | inspect (p.to zero)
    ...   | zero , s | zero , t = absurdp' (fzero≠fsuc a (≡.trans t to-suc))
      where
      to-suc : p.to zero ≡ suc a
      to-suc = ≡.trans (≡.cong p.to q) (p.linv (suc a))
    ...   | zero , s | suc c , t = Fin-suc-injective (≡.trans t (≡.trans (≡.cong p.to q) (p.linv (suc a))))
    ...   | suc b , s | v , t = absurdp' (fzero≠fsuc b (≡.sym (≡.trans s to-zero)))
      where
      to-zero : p.to (suc u) ≡ zero
      to-zero = ≡.trans (≡.cong p.to r) (p.linv zero)
    linv a | suc b , q | v , r with inspect (p.to (suc b)) | inspect (p.to zero)
    ...   | zero , s | w = absurdp' (fzero≠fsuc a (≡.trans s to-suc))
      where
      to-suc : p.to (suc b) ≡ suc a
      to-suc = ≡.trans (≡.cong p.to q) (p.linv (suc a))
    ...   | suc c , s | w = Fin-suc-injective (≡.trans s (≡.trans (≡.cong p.to q) (p.linv (suc a))))
    rinv : (a : Fin m) → from (to a) ≡ a
    rinv a with inspect (p.to (suc a)) | inspect (p.to zero)
    ... | zero , q | zero , r = absurdp' (fzero≠fsuc a eq)
      where
      eq : zero ≡ suc a
      eq = ≡.trans (≡.sym (≡.trans (≡.cong p.from r) (p.rinv zero)))
                    (≡.trans (≡.cong p.from q) (p.rinv (suc a)))
    ... | zero , q | suc u , r with inspect (p.from (suc u)) | inspect (p.from zero)
    ...   | zero , s | zero , t = absurdp' (fzero≠fsuc a (≡.trans t from-suc))
      where
      from-suc : p.from zero ≡ suc a
      from-suc = ≡.trans (≡.cong p.from q) (p.rinv (suc a))
    ...   | zero , s | suc c , t = Fin-suc-injective (≡.trans t (≡.trans (≡.cong p.from q) (p.rinv (suc a))))
    ...   | suc b , s | v , t = absurdp' (fzero≠fsuc b (≡.sym (≡.trans s from-zero)))
      where
      from-zero : p.from (suc u) ≡ zero
      from-zero = ≡.trans (≡.cong p.from r) (p.rinv zero)
    rinv a | suc b , q | v , r with inspect (p.from (suc b)) | inspect (p.from zero)
    ...   | zero , s | w = absurdp' (fzero≠fsuc a (≡.trans s from-suc))
      where
      from-suc : p.from (suc b) ≡ suc a
      from-suc = ≡.trans (≡.cong p.from q) (p.rinv (suc a))
    ...   | suc c , s | w = Fin-suc-injective (≡.trans s (≡.trans (≡.cong p.from q) (p.rinv (suc a))))

Fin↔-injective : ∀ {m n} → Fin m ↔ Fin n → m ≡ n
Fin↔-injective {zero} {zero} p = ≡.refl
Fin↔-injective {zero} {suc n} p = absurdp' (¬Fin0 ∣ from zero ∣)
  where open _↔_ p
Fin↔-injective {suc m} {zero} p = absurdp' (¬Fin0 ∣ to zero ∣)
  where open _↔_ p
Fin↔-injective {suc m} {suc n} p = ≡.cong suc (Fin↔-injective (Fin↔-suc p))

open import QIT.Set.Bijection
Fin-inj→≤ : ∀ {m n} → (f : Fin m → Fin n) → IsInjection f → m ℕ.≤ n
Fin-inj→≤ {zero} {zero} f f-inj = z≤n
Fin-inj→≤ {zero} {suc n} f f-inj = z≤n
Fin-inj→≤ {suc m} {zero} f f-inj = absurdp (¬Fin0 ∣ f zero ∣)
Fin-inj→≤ {suc m} {suc n} f f-inj = s≤s (Fin-inj→≤ g g-inj)
  where
  g : Fin m → Fin n
  g a with inspect (f (suc a)) | inspect (f zero)
  ... | zero , p | zero , q =
    absurdp (fzero≠fsuc a (f-inj (≡.trans (≡.sym q) p)))
  ... | zero , _ | suc c , _ = c
  ... | suc d , _ | _ = d
  g-inj : IsInjection g
  g-inj {a} {b} s with inspect (f zero) | inspect (f (suc a)) | inspect (f (suc b))
  ... | zero , p | zero , q | _ =
    absurdp' (fzero≠fsuc a (f-inj (≡.trans (≡.sym p) q)))
  ... | zero , p | suc d , _ | zero , r =
    absurdp' (fzero≠fsuc b (f-inj (≡.trans (≡.sym p) r)))
  ... | zero , p | suc d , q | suc e , r =
    Fin-suc-injective (f-inj (≡.trans (≡.sym q) (≡.trans (≡.cong suc s) r)))
  ... | suc c , p | zero , q | zero , r =
    Fin-suc-injective (f-inj (≡.trans (≡.sym q) r))
  ... | suc c , p | zero , q | suc e , r =
    absurdp' (fzero≠fsuc b (f-inj (≡.trans (≡.sym p) (≡.trans (≡.cong suc s) r))))
  ... | suc c , p | suc d , q | zero , r =
    absurdp' (fzero≠fsuc a (f-inj (≡.trans (≡.sym p) (≡.trans (≡.cong suc (≡.sym s)) q))))
  ... | suc c , p | suc d , q | suc e , r =
    Fin-suc-injective (f-inj (≡.trans (≡.sym q) (≡.trans (≡.cong suc s) r)))

≤-antisym : ∀ {m n} → m ℕ.≤ n → n ℕ.≤ m → m ≡ n 
≤-antisym z≤n       z≤n       = ≡.refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = ≡.cong suc (≤-antisym m≤n n≤m)

cantor-schröder-bernstein : ∀ {m n} → (f : Fin m → Fin n) (g : Fin n → Fin m) →
                            IsInjection f → IsInjection g →
                            m ≡ n
cantor-schröder-bernstein f g f-inj g-inj = ≤-antisym
  (Fin-inj→≤ f f-inj) (Fin-inj→≤ g g-inj)

open import QIT.Relation.WellFounded


≤refl-ℕ : ∀ {m} → m ℕ.≤ m
≤refl-ℕ {zero} = z≤n
≤refl-ℕ {suc m} = s≤s ≤refl-ℕ

≤suc-ℕ : ∀ {m} → m ℕ.≤ suc m
≤suc-ℕ {zero} = z≤n
≤suc-ℕ {suc m} = s≤s ≤suc-ℕ

≤trans-ℕ : ∀ {l m n} → l ℕ.≤ m → m ℕ.≤ n → l ℕ.≤ n
≤trans-ℕ z≤n q = z≤n
≤trans-ℕ (s≤s p) (s≤s q) = s≤s (≤trans-ℕ p q)

minℕ : ∀ {ℓP} → (P : ℕ → Prop ℓP)
     → (∀ n → Decᵖ (P n))
     → ∃ P
     → ∃ (λ n → P n ∧ ∀ m → P m → ∥ n ℕ.≤ m ∥)
minℕ P decP ∣ n , pn ∣ = rec n ∣ n , pn , ∣ ≤refl-ℕ ∣ ∣
  where
  P' : ℕ → Prop _
  P' m = ∃ λ n → P n ∧ ∥ n ℕ.≤ m ∥
  decP' : (n : ℕ) → Decᵖ (P' n)
  decP' zero with decP 0
  ... | yes p0 = yes ∣ 0 , p0 , ∣ z≤n ∣ ∣
  ... | no ¬p0 = no λ {(∣ 0 , p0 , ∣ z≤n ∣ ∣) → ¬p0 p0}
  decP' (suc n) with decP' n | decP (suc n)
  ... | yes p<n | _ = yes (u p<n)
    where
    u : P' n → P' (suc n)
    u ∣ m , pm , ∣ m≤n ∣ ∣ = ∣ m , pm , ∣ ≤trans-ℕ m≤n ≤suc-ℕ ∣ ∣
  ... | no ¬p<n | yes pn' = yes ∣ suc n , pn' , ∣ ≤refl-ℕ ∣ ∣
  ... | no ¬p<n | no ¬pn' = no ¬p<n'
    where
    ¬p<n' : ¬ P' (suc n)
    ¬p<n' ∣ m , pm , ∣ m≤n' ∣ ∣ with m ≟ℕ suc n
    ... | yes ≡.refl = ¬pn' pm
    ... | no m≠n' = ¬p<n ∣ {!!} ∣
  rec : (max : ℕ)
      → ∃ (λ n → P n ∧ ∥ n ℕ.≤ max ∥)
      → ∃ (λ n → P n ∧ ∀ m → P m → ∥ n ℕ.≤ m ∥)
  rec max ∣ zero , pn , n≤max ∣ = ∣ zero , pn , (λ m z → ∣ z≤n ∣) ∣
  rec max ∣ suc n , psn , n≤max ∣ with decP n
  ... | yes pn = rec n ∣ n , pn , ∣ ≤refl-ℕ ∣ ∣
  ... | no ¬pn = ∣ {!!} ∣

-- minℕ {ℓP} P decP inhabP with decP 0
-- ... | yes p = 0 , p
-- ... | no ¬p =
--   let P' : ℕ → Prop ℓP
--       P' m = P (suc m)
--       decP' : (n : ℕ) → Decᵖ (P (suc n))
--       decP' n = decP (suc n)
--       inhab-suc : ∥ ΣP ℕ P ∥ → ∥ ΣP ℕ P' ∥
--       inhab-suc ∣ m , p ∣ = {!!}
--       inhabP' : ∥ ΣP ℕ P' ∥
--       inhabP' = {!!}
--       n , q = minℕ P' decP' {!inhabP'!}
--   in {!!}
