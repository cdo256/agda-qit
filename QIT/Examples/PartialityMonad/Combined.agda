module QIT.Examples.PartialityMonad.Combined where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

open import QIT.Examples.PartialityMonad.Erased
open import QIT.Examples.PartialityMonad.WellFormed

Seq : Set
Seq = Σ Seq0 Seq1

A⊥ : Set
A⊥ = Σ A⊥0 A⊥1

_≤_ : A⊥ → A⊥ → Set
(x0 , x1) ≤ (y0 , y1) = Σ ≤0 (λ p0 → x0 ≤1 y0 ⊣ p0)

_≈_ : A⊥ → A⊥ → Set
(x0 , x1) ≈ (y0 , y1) = Σ ≈0 (λ e0 → x0 ≈1 y0 ⊣ e0)

η : Bool → A⊥
η b = η0 b , η1 b

⊥ : A⊥
⊥ = ⊥0 , ⊥1

⨆ : Seq → A⊥
⨆ (a0 , a1) = ⨆0 a0 , ⨆1 a1

⟦_⟧ : Seq → ℕ → A⊥
⟦ a0 , a1 ⟧ n = ⟦ a0 ⟧0 n , ⟦ a1 ⟧1 n

_⸴_ : (f : ℕ → A⊥) → ((i : ℕ) → f i ≤ f (suc i)) → Seq
f ⸴ f≤ =
  ( (λ i → proj₁ (f i)) ,0 (λ i → proj₁ (f≤ i)) )
  ,
  (,1 (λ i → proj₁ (f i)) (λ i → proj₁ (f≤ i))
      (λ i → proj₂ (f i))
      (λ i → proj₂ (f≤ i)) )

≤refl : ∀ {x} → x ≤ x
≤refl {(x0 , x1)} = ≤refl0 x0 , ≤refl1 x1

≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans {(x0 , x1)} {(y0 , y1)} {(z0 , z1)} (p0 , p1) (q0 , q1) =
  ≤trans0 x0 y0 z0 p0 q0 , ≤trans1 p1 q1

⊥≤ : ∀ {x} → ⊥ ≤ x
⊥≤ {(x0 , x1)} = ⊥≤0 x0 , ⊥≤1 x1

≤⨆ : ∀ a i → ⟦ a ⟧ i ≤ ⨆ a
≤⨆ (a0 , a1) i = ≤⨆0 a0 i , ≤⨆1 a1 i

⨆≤ : ∀ a x → (∀ i → ⟦ a ⟧ i ≤ x) → ⨆ a ≤ x
⨆≤ (a0 , a1) (x0 , x1) p =
  ⨆≤0 a0 x0 (λ i → proj₁ (p i))
  ,
  ⨆≤1 a1 x1
      (λ i → proj₁ (p i))
      (λ i → proj₂ (p i))

inc : (a : Seq) → ∀ i → ⟦ a ⟧ i ≤ ⟦ a ⟧ (suc i)
inc (a0 , a1) i = inc0 a0 i , inc1 a1 i

≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
≈antisym {(x0 , x1)} {(y0 , y1)} (p0 , p1) (q0 , q1) =
  ≈antisym0 x0 y0 p0 q0 , ≈antisym1 p1 q1

≈refl : ∀ {x} → x ≈ x
≈refl {x} = ≈antisym {x} {x} (≤refl {x}) (≤refl {x})

≈sym : ∀ {x y} → x ≈ y → y ≈ x
≈sym {x} {y}
  (≈antisym0 _ _ p0 q0 , ≈antisym1 p1 q1)
  = ≈antisym {y} {x} (q0 , q1) (p0 , p1)

≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈trans {x} {y} {z}
  (≈antisym0 _ _ p0 q0 , ≈antisym1 p1 q1)
  (≈antisym0 _ _ r0 s0 , ≈antisym1 r1 s1)
  = ≈antisym {x} {z} (≤trans {x} {y} {z} (p0 , p1) (r0 , r1))
                     (≤trans {z} {y} {x} (s0 , s1) (q0 , q1))

≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
≤cong {x} {x'} {y} {y'}
  (≈antisym0 _ _ x≤x' x'≤x , ≈antisym1 p q)
  (≈antisym0 _ _ y≤y' y'≤y , ≈antisym1 r s)
  x≤y
  = ≤trans {x'} {x} {y'} (x'≤x , q)
    (≤trans {x} {y} {y'} x≤y (y≤y' , r))

