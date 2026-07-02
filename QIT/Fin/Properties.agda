open import QIT.Prelude

module QIT.Fin.Properties ⦃ pathElim* : PathElim ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Function.Base 
-- open import Data.Fin as Fin hiding (_≟_; pred) public
-- open import Data.Nat as ℕ renaming (_>_ to _>ᴺ_)
-- open import Data.Nat.Properties as ℕₚ using (≤-total)
open import QIT.Fin.Base
open import QIT.Nat

inhab⇔>0 : ∀ {n} → ∥ Fin n ∥ ⇔ (n > 0)
inhab⇔>0 {zero} .∧e₁ ∣ () ∣
inhab⇔>0 {zero} .∧e₂ ()
inhab⇔>0 {suc n} .∧e₁ _ = s≤s z≤n
inhab⇔>0 {suc n} .∧e₂ _ = ∣ zero ∣

≅to⇔ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → A ≅ˢ B → ∥ A ∥ ⇔ ∥ B ∥
≅to⇔ {A = A} {B} p .∧e₁ ∣ x ∣ = ∣ p .≅ˢ.to x ∣
≅to⇔ {A = A} {B} p .∧e₂ ∣ y ∣ = ∣ p .≅ˢ.from y ∣

¬Fin0 : ¬ ∥ Fin 0 ∥
¬Fin0 ∣ () ∣

fzero≠fsuc : ∀ {n} (a : Fin n) → zero ≢ suc a
fzero≠fsuc a ()

Fin≅-suc : ∀ {m n} → Fin (suc m) ≅ˢ Fin (suc n) → Fin m ≅ˢ Fin n
Fin≅-suc {m} {n} p = q
  where
  f' : ∀ {m n} → (p : Fin (suc m) ≅ˢ Fin (suc n)) → (a : Fin m) → Singleton (p .≅ˢ.to (suc a)) → Singleton (p .≅ˢ.to zero) → Fin n
  f' p a (zero , q) (zero , r) =
    ⊥e' (fzero≠fsuc a (≡.trans (≡.sym (p.rinv zero))
                           (≡.trans (≡.cong p.from (≡.trans (≡.sym r) q))
                            (p.rinv (suc a)))))
    where module p = _≅ˢ_ p
  f' p a (zero , _) (suc c , _) = c
  f' p a (suc b , _) _ = b

  f : ∀ {m n} → (p : Fin (suc m) ≅ˢ Fin (suc n)) → (a : Fin m) → Fin n
  f p a = f' p a (inspect (p .≅ˢ.to (suc a))) (inspect (p .≅ˢ.to zero))
    where module p = _≅ˢ_ p

  module p = _≅ˢ_ p
  q : Fin m ≅ˢ Fin n
  q = record
    { to = to
    ; from = from
    ; rinv = rinv
    ; linv = linv }
    where
    to : Fin m → Fin n
    to = f p
    from : Fin n → Fin m
    from = f (≅ˢ.sym p)
    linv : (a : Fin n) → to (from a) ≡ a
    linv a with inspect (p.from (suc a)) | inspect (p.from zero)
    ... | zero , q | zero , r = ⊥e (fzero≠fsuc a eq)
      where
      eq : zero ≡ suc a
      eq = ≡.trans (≡.sym (≡.trans (≡.cong p.to r) (p.linv zero)))
                    (≡.trans (≡.cong p.to q) (p.linv (suc a)))
    ... | zero , q | suc u , r with inspect (p.to (suc u)) | inspect (p.to zero)
    ...   | zero , s | zero , t = ⊥e (fzero≠fsuc a (≡.trans t to-suc))
      where
      to-suc : p.to zero ≡ suc a
      to-suc = ≡.trans (≡.cong p.to q) (p.linv (suc a))
    ...   | zero , s | suc c , t = Fin-suc-injective (≡.trans t (≡.trans (≡.cong p.to q) (p.linv (suc a))))
    ...   | suc b , s | v , t = ⊥e (fzero≠fsuc b (≡.sym (≡.trans s to-zero)))
      where
      to-zero : p.to (suc u) ≡ zero
      to-zero = ≡.trans (≡.cong p.to r) (p.linv zero)
    linv a | suc b , q | v , r with inspect (p.to (suc b)) | inspect (p.to zero)
    ...   | zero , s | w = ⊥e (fzero≠fsuc a (≡.trans s to-suc))
      where
      to-suc : p.to (suc b) ≡ suc a
      to-suc = ≡.trans (≡.cong p.to q) (p.linv (suc a))
    ...   | suc c , s | w = Fin-suc-injective (≡.trans s (≡.trans (≡.cong p.to q) (p.linv (suc a))))
    rinv : (a : Fin m) → from (to a) ≡ a
    rinv a with inspect (p.to (suc a)) | inspect (p.to zero)
    ... | zero , q | zero , r = ⊥e (fzero≠fsuc a eq)
      where
      eq : zero ≡ suc a
      eq = ≡.trans (≡.sym (≡.trans (≡.cong p.from r) (p.rinv zero)))
                    (≡.trans (≡.cong p.from q) (p.rinv (suc a)))
    ... | zero , q | suc u , r with inspect (p.from (suc u)) | inspect (p.from zero)
    ...   | zero , s | zero , t = ⊥e (fzero≠fsuc a (≡.trans t from-suc))
      where
      from-suc : p.from zero ≡ suc a
      from-suc = ≡.trans (≡.cong p.from q) (p.rinv (suc a))
    ...   | zero , s | suc c , t = Fin-suc-injective (≡.trans t (≡.trans (≡.cong p.from q) (p.rinv (suc a))))
    ...   | suc b , s | v , t = ⊥e (fzero≠fsuc b (≡.sym (≡.trans s from-zero)))
      where
      from-zero : p.from (suc u) ≡ zero
      from-zero = ≡.trans (≡.cong p.from r) (p.rinv zero)
    rinv a | suc b , q | v , r with inspect (p.from (suc b)) | inspect (p.from zero)
    ...   | zero , s | w = ⊥e (fzero≠fsuc a (≡.trans s from-suc))
      where
      from-suc : p.from (suc b) ≡ suc a
      from-suc = ≡.trans (≡.cong p.from q) (p.rinv (suc a))
    ...   | suc c , s | w = Fin-suc-injective (≡.trans s (≡.trans (≡.cong p.from q) (p.rinv (suc a))))

Fin↔-injective : ∀ {m n} → Fin m ≅ˢ Fin n → m ≡ n
Fin↔-injective {zero} {zero} p = ≡.refl
Fin↔-injective {zero} {suc n} p = ⊥e (¬Fin0 ∣ from zero ∣)
  where open _≅ˢ_ p
Fin↔-injective {suc m} {zero} p = ⊥e (¬Fin0 ∣ to zero ∣)
  where open _≅ˢ_ p
Fin↔-injective {suc m} {suc n} p = ≡.cong suc (Fin↔-injective (Fin≅-suc p))

open import QIT.Set.Bijection
Fin-inj→≤ : ∀ {m n} → (f : Fin m → Fin n) → IsInjection f → m ≤ n
Fin-inj→≤ {zero} {zero} f f-inj = z≤n
Fin-inj→≤ {zero} {suc n} f f-inj = z≤n
Fin-inj→≤ {suc m} {zero} f f-inj = ⊥e (¬Fin0 ∣ f zero ∣)
Fin-inj→≤ {suc m} {suc n} f f-inj = s≤s (Fin-inj→≤ g g-inj)
  where
  g : Fin m → Fin n
  g a with inspect (f (suc a)) | inspect (f zero)
  ... | zero , p | zero , q =
    ⊥e' (fzero≠fsuc a (f-inj (≡.trans (≡.sym q) p)))
  ... | zero , _ | suc c , _ = c
  ... | suc d , _ | _ = d
  g-inj : IsInjection g
  g-inj {a} {b} s with inspect (f zero) | inspect (f (suc a)) | inspect (f (suc b))
  ... | zero , p | zero , q | _ =
    ⊥e (fzero≠fsuc a (f-inj (≡.trans (≡.sym p) q)))
  ... | zero , p | suc d , _ | zero , r =
    ⊥e (fzero≠fsuc b (f-inj (≡.trans (≡.sym p) r)))
  ... | zero , p | suc d , q | suc e , r =
    Fin-suc-injective (f-inj (≡.trans (≡.sym q) (≡.trans (≡.cong suc s) r)))
  ... | suc c , p | zero , q | zero , r =
    Fin-suc-injective (f-inj (≡.trans (≡.sym q) r))
  ... | suc c , p | zero , q | suc e , r =
    ⊥e (fzero≠fsuc b (f-inj (≡.trans (≡.sym p) (≡.trans (≡.cong suc s) r))))
  ... | suc c , p | suc d , q | zero , r =
    ⊥e (fzero≠fsuc a (f-inj (≡.trans (≡.sym p) (≡.trans (≡.cong suc (≡.sym s)) q))))
  ... | suc c , p | suc d , q | suc e , r =
    Fin-suc-injective (f-inj (≡.trans (≡.sym q) (≡.trans (≡.cong suc s) r)))

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n 
≤-antisym z≤n       z≤n       = ≡.refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = ≡.cong suc (≤-antisym m≤n n≤m)

cantor-schröder-bernstein : ∀ {m n} → (f : Fin m → Fin n) (g : Fin n → Fin m) →
                            IsInjection f → IsInjection g →
                            m ≡ n
cantor-schröder-bernstein f g f-inj g-inj = ≤-antisym
  (Fin-inj→≤ f f-inj) (Fin-inj→≤ g g-inj)

open import QIT.Relation.WellFounded


≤refl-ℕ : ∀ {m} → m ≤ m
≤refl-ℕ {zero} = z≤n
≤refl-ℕ {suc m} = s≤s ≤refl-ℕ

≤suc-ℕ : ∀ {m} → m ≤ suc m
≤suc-ℕ {zero} = z≤n
≤suc-ℕ {suc m} = s≤s ≤suc-ℕ

≤trans-ℕ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤trans-ℕ z≤n q = z≤n
≤trans-ℕ (s≤s p) (s≤s q) = s≤s (≤trans-ℕ p q)

≤suc∧≢→≤ : ∀ {m n} → m ≤ suc n → m ≢ suc n → m ≤ n
≤suc∧≢→≤ {zero} m≤sn m≢sn = z≤n
≤suc∧≢→≤ {suc zero} {zero} (s≤s z≤n) m≢sn = ⊥e (m≢sn ≡.refl)
≤suc∧≢→≤ {suc (suc m)} {zero} (s≤s ()) m≢sn
≤suc∧≢→≤ {suc m} {suc n} (s≤s m≤sn) m≢sn =
  s≤s (≤suc∧≢→≤ m≤sn (λ q → m≢sn (≡.cong suc q)))

minℕ : ∀ {ℓP} → (P : ℕ → Prop ℓP)
     → (∀ n → Decᵖ (P n))
     → ∃ P
     → ∃ (λ n → P n ∧ ∀ m → P m → n ≤ m)
minℕ P decP (∃i n , pn) = rec n (∃i n , ∧i pn , ≤refl-ℕ)
  where
  P' : ℕ → Prop _
  P' m = ∃ λ n → P n ∧ (n ≤ m)
  decP' : (n : ℕ) → Decᵖ (P' n)
  decP' zero with decP 0
  ... | yes p0 = yes (∃i 0 , (∧i p0 , z≤n))
  ... | no ¬p0 = no λ {(∃i 0 , (∧i p0 , z≤n)) → ¬p0 p0}
  decP' (suc n) with decP' n | decP (suc n)
  ... | yes p<n | _ = yes (u p<n)
    where
    u : P' n → P' (suc n)
    u (∃i m , (∧i pm , m≤n)) = ∃i m , ∧i pm , ≤trans-ℕ m≤n ≤suc-ℕ
  ... | no ¬p<n | yes pn' = yes (∃i (suc n) , ∧i pn' , ≤refl-ℕ)
  ... | no ¬p<n | no ¬pn' = no ¬p<n'
    where
    ¬p<n' : ¬ P' (suc n)
    ¬p<n' (∃i m , ∧i pm , m≤n') with m ≟ℕ suc n
    ... | yes ≡.refl = ¬pn' pm
    ... | no m≠n' = ¬p<n (∃i m , ∧i pm , ≤suc∧≢→≤ m≤n' m≠n')
  least : ∀ {max} → ¬ P' max → ∀ m → P m → suc max ≤ m
  least {max} ¬p< m pm with ≤-total m (suc max)
  ... | ∨i₂ sn≤m = sn≤m
  ... | ∨i₁ m≤sn with m ≟ℕ suc max
  ...   | yes ≡.refl = ≤refl-ℕ
  ...   | no m≢sn = ⊥e (¬p< (∃i m , ∧i pm , ≤suc∧≢→≤ m≤sn m≢sn))
  rec : (max : ℕ)
      → ∃ (λ n → P n ∧ n ≤ max)
      → ∃ (λ n → P n ∧ ∀ m → P m → n ≤ m)
  rec zero (∃i zero , ∧i pn , n≤max) = ∃i zero , ∧i pn , (λ m z → z≤n)
  rec zero (∃i (suc n) , (∧i pn , ()))
  rec (suc max) ex with decP' max
  ... | yes p< = rec max p<
  ... | no ¬p< with ex
  ...   | ∃i zero , (∧i p0 , z≤n) = ⊥e (¬p< (∃i zero , ∧i p0 , z≤n))
  ...   | ∃i (suc n) , ∧i psn , n≤max with n ≟ℕ max
  ...     | yes ≡.refl = ∃i (suc max) , ∧i psn , least ¬p<
  ...     | no n≠max = ⊥e (¬p< (∃i (suc n) , (∧i psn , ≤suc∧≢→≤ n≤max (λ q → n≠max (ℕ-suc-injective q)))))
