module QIT.Examples.Surreal where
open import QIT.Prelude
open import Data.Nat using (ℕ)
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Set.Base

interleaved mutual
  data S : Set₁
  data _<_ : S → S → Prop₁
  data _≤_ : S → S → Prop₁
  neg : S → S
  Subset : Set₁
  Subset = Σ Set (λ I → I → S)
  _∈_ : S → Subset → Prop₁
  x ∈ (I , A) = ∃ λ i → A i ≡ x
  _≤ˢ_ : Subset → Subset → Prop₁
  (I , A) ≤ˢ (J , B) = ∀ (i : I) (j : J) → A i < B j
  data _ where
    _∣_∶_ : (l r : Subset) → l ≤ˢ r → S
    neg< : {x y : S} → x < y → neg y < neg x 
    <i : ∀ {l1 l2 r1 r2 : Subset} {l1≤r1 : l1 ≤ˢ r1} {l2≤r2 : l2 ≤ˢ r2}
        → (x y : S) → x ∈ r1 → y ∈ l2 → x ≤ y
        → (l1 ∣ r1 ∶ l1≤r1) < (l2 ∣ r2 ∶ l2≤r2) 
    <l : ∀ {l r : Subset} {l≤r : l ≤ˢ r}
       → (x : S) → x ∈ l 
       → x < (l ∣ r ∶ l≤r)
    <r : ∀ {l r : Subset} {l≤r : l ≤ˢ r}
       → (x : S) → x ∈ r
       → (l ∣ r ∶ l≤r) < x
    <→≤ : ∀ x y → x < y → x ≤ y
    ≤refl : ∀ {x : S} → x ≤ x

  negˢ : Subset → Subset
  negᵖ : (l r : Subset) → l ≤ˢ r → negˢ r ≤ˢ negˢ l
  neg (l ∣ r ∶ l<r) = negˢ r ∣ negˢ l ∶ negᵖ l r l<r
    
  negˢ-p : ∀ {I A} → (I , λ i → neg (A i)) ≡ negˢ (I , A)
  negˢ-pI : ∀ {I A} → I ≡ proj₁ (negˢ (I , A))
  negˢ-p' : ∀ {I A} → ∀ i
        → neg (A i) ≡ proj₂ (negˢ (I , A)) (subst (λ ○ → ○) negˢ-pI i)
  negˢ (I , A) = I , λ i → neg (A i)
  negᵖ (I , A) (J , B) A≤B j i =
    p ≡.refl ≡.refl ≡.refl ≡.refl
    where
    p : proj₁ (negˢ (I , A)) ≡ I
      → proj₁ (negˢ (J , B)) ≡ J
      → proj₂ (negˢ (I , A)) i ≡ neg (A i)
      → proj₂ (negˢ (J , B)) j ≡ neg (B j)
      → neg (B j) < neg (A i)
    p ≡.refl ≡.refl ≡.refl ≡.refl = neg< (A≤B i j)
  negˢ-p {I} {A} = ≡.refl
  negˢ-pI = ≡.refl 
  negˢ-p' {I} {A} i = ≡.refl

    
∅ : Subset
∅ = ⊥ , λ ()

⟨_⟩ : S → Subset
⟨ x ⟩ = ⊤ , λ _ → x

z : S
z = ∅ ∣ ∅ ∶ λ ()

suc : S → S
suc x = ⟨ x ⟩ ∣ ∅ ∶ λ i ()

pred : S → S
pred x = ∅ ∣ ⟨ x ⟩ ∶ λ ()

ℕ→S : ℕ → S
ℕ→S ℕ.zero = z
ℕ→S (ℕ.suc n) = ⟨ ℕ→S n ⟩ ∣ ∅ ∶ λ _ ()

N : Subset
N = ℕ , ℕ→S

data ℤ : Set where
  zpos : ℕ → ℤ
  zzero : ℤ
  zneg : ℕ → ℤ

zpred : ℤ → ℤ  
zpred (zpos ℕ.zero) = zzero
zpred (zpos (ℕ.suc n)) = zpos n
zpred zzero = zneg ℕ.zero
zpred (zneg n) = zneg (ℕ.suc n)

zsuc : ℤ → ℤ  
zsuc (zneg ℕ.zero) = zzero
zsuc (zneg (ℕ.suc n)) = zneg n
zsuc zzero = zneg ℕ.zero
zsuc (zpos n) = zpos (ℕ.suc n)

ℤ→S : ℤ → S
ℤ→S (zpos n) = ℕ→S (ℕ.suc n)
ℤ→S zzero = z
ℤ→S (zneg n) = neg (ℕ→S (ℕ.suc n))

x<sucx : ∀ x → x < suc x
x<sucx (l ∣ r ∶ l<r) = <l (l ∣ r ∶ l<r) ∣ tt , ≡.refl ∣

ω : S
ω = N ∣ ∅ ∶ λ _ ()

lim+ : (ℕ → S) → S
lim+ a = (ℕ , a) ∣ ∅ ∶ λ _ ()

lim- : (ℕ → S) → S
lim- a = ∅ ∣ (ℕ , a) ∶ λ ()

1/2 : S
1/2 = ⟨ z ⟩ ∣ ⟨ ℕ→S 1 ⟩ ∶ p
  where
  p : ⟨ z ⟩ ≤ˢ ⟨ ℕ→S 1 ⟩
  p tt tt = <l z ∣ tt , ≡.refl ∣
