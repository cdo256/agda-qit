module QIT.Examples.CauchyReals where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹 
open 𝔹 using (Bool; false; true)

import Data.Integer as ℤ 
open ℤ using (ℤ; 0ℤ; 1ℤ)

module ℚ where
  import Data.Rational.Base
  import Data.Rational.Properties
  open Data.Rational.Base public
  open Data.Rational.Properties
    using (positive⁻¹; +-identityʳ; +-monoˡ-<; +-monoʳ-<) public

open ℚ using (ℚ; 0ℚ; 1ℚ)

private
  _>0 : ℚ → Set
  _>0 = ℚ.Positive

record IsCauchy (s : ℕ → ℚ) : Set where
  field
    upper : ℕ → ℚ
    lower : ℕ → ℚ
    s>u : ∀ n → s n ℚ.< upper n
    l<s : ∀ n → lower n ℚ.< s n
    cauchy : ∀ ε → ε >0 → ∃ λ n → ∀ m → m ℕ.> n
           → ∥ ℚ.∣ upper m ℚ.- lower m ∣ ℚ.< ε ∥

ℝ = ΣP (ℕ → ℚ) (Trunc₁ IsCauchy)

data _≈_ : (a b : ℝ) → Prop where
  ≈bisim : ∀ a b → (∀ ε → ε >0 → ∃ λ n → ∀ m → m ℕ.> n
         → ∥ ℚ.∣ a .fst m ℚ.- b .fst m ∣ ℚ.< ε ∥) → a ≈ b

data _<_ : (a b : ℝ) → Prop where
  <intro : ∀ (a b : ℕ → ℚ)  {a-cauchy : IsCauchy a} {b-cauchy : IsCauchy b}
         → (i : ℕ) → a-cauchy .IsCauchy.upper i ℚ.< b-cauchy .IsCauchy.lower i
         → (a , ∣ a-cauchy ∣) < (b , ∣ b-cauchy ∣)

data _≤_ : (a b : ℝ) → Prop where
  ≤intro : ∀ (a b : ℕ → ℚ)  {a-cauchy : IsCauchy a} {b-cauchy : IsCauchy b}
         → (∀ (i : ℕ)
           → a-cauchy .IsCauchy.lower i ℚ.≤ b-cauchy .IsCauchy.upper i)
         → (a , ∣ a-cauchy ∣) ≤ (b , ∣ b-cauchy ∣)

x>0→q<q+x : ∀ (x q : ℚ) → x >0 → q ℚ.< q ℚ.+ x
x>0→q<q+x x q x>0 =
  ≡.subst (ℚ._< q ℚ.+ x)
          (≡ˢ→≡ (ℚ.+-identityʳ q))
          q+0<q+x
  where
  0<x : 0ℚ ℚ.< x
  0<x = ℚ.positive⁻¹ x ⦃ x>0 ⦄
  q+0<q+x : q ℚ.+ 0ℚ ℚ.< q ℚ.+ x
  q+0<q+x = ℚ.+-monoʳ-< q 0<x

postulate
  x>0→q-x<q : ∀ (x q : ℚ) → x >0 → q ℚ.- x ℚ.< q

  1/suc>0 : ∀ (i : ℕ) → (1ℤ ℚ./ suc i) >0

  dist-simplify : ∀ (q x : ℚ) → x >0
                → ℚ.∣ (q ℚ.+ x) ℚ.- (q ℚ.- x) ∣ ≡ x ℚ.+ x

  archimedean : ∀ (ε : ℚ) → ε >0
              → ∃ λ n → ∀ m → m ℕ.> n
              → ∥ (1ℤ ℚ./ suc m) ℚ.+ (1ℤ ℚ./ suc m) ℚ.< ε ∥

constIsCauchy : ∀ (q : ℚ) → ∥ IsCauchy (λ _ → q) ∥
constIsCauchy q = ∣ record
  { upper = λ i → q ℚ.+ (1ℤ ℚ./ suc i)
  ; lower = λ i → q ℚ.- (1ℤ ℚ./ suc i)
  ; s>u = λ i → x>0→q<q+x (1ℤ ℚ./ suc i) q (1/suc>0 i)
  ; l<s = λ i → x>0→q-x<q (1ℤ ℚ./ suc i) q (1/suc>0 i)
  ; cauchy = λ ε ε>0 → map-cauchy ε (archimedean ε ε>0)
  } ∣
  where
  map-cauchy : ∀ ε → ∃ (λ n → ∀ m → m ℕ.> n → ∥ (1ℤ ℚ./ suc m) ℚ.+ (1ℤ ℚ./ suc m) ℚ.< ε ∥)
             → ∃ (λ n → ∀ m → m ℕ.> n → ∥ ℚ.∣ (q ℚ.+ (1ℤ ℚ./ suc m)) ℚ.- (q ℚ.- (1ℤ ℚ./ suc m)) ∣ ℚ.< ε ∥)
  map-cauchy ε ∣ n , bounds ∣ = ∣ (n , λ m m>n → 
    ≡.substp (λ dist → ∥ dist ℚ.< ε ∥)
            (≡.sym (dist-simplify q (1ℤ ℚ./ suc m) (1/suc>0 m)))
            (bounds m m>n)) ∣


ℚ→ℝ : ℚ → ℝ
ℚ→ℝ q = (λ _ → q) , constIsCauchy q

0ᴿ : ℝ
0ᴿ = ℚ→ℝ 0ℚ

1ᴿ : ℝ
1ᴿ = ℚ→ℝ 1ℚ
  
]0,1[ : ℝ → Prop
]0,1[ x = 0ᴿ < x ∧ x < 1ᴿ 

Interval : ℚ → ℚ → ℝ → Prop

[0,1] : ℝ → Prop
[0,1] x = 0ᴿ ≤ x ∧ x ≤ 1ᴿ 
