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

⨆ : (a : ℕ → A⊥) (a-inc : ∀ i → a i ≤ a (suc i)) → A⊥
⨆ a a-inc = ⨆0 a0 a-inc0 , ⨆1 a1 a-inc1
  where
  a0 : ℕ → A⊥0
  a0 i = a i .proj₁
  a1 : ∀ i → A⊥1 (a0 i)
  a1 i = a i .proj₂ 
  a-inc0 : ℕ → ≤0
  a-inc0 i = a-inc i .proj₁
  a-inc1 : ∀ i → a0 i ≤1 a0 (suc i) ⊣ a-inc0 i
  a-inc1 i = a-inc i .proj₂ 

≤refl : ∀ {x} → x ≤ x
≤refl {(x0 , x1)} = ≤refl0 x0 , ≤refl1 x1

≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans {(x0 , x1)} {(y0 , y1)} {(z0 , z1)} (p0 , p1) (q0 , q1) =
  ≤trans0 x0 y0 z0 p0 q0 , ≤trans1 x1 y1 z1 p1 q1

⊥≤ : ∀ {x} → ⊥ ≤ x
⊥≤ {(x0 , x1)} = ⊥≤0 x0 , ⊥≤1 x1

≤⨆ : ∀ a a-inc i → a i ≤ ⨆ a a-inc
≤⨆ a a-inc i =
    ≤⨆0 a0 a-inc0 i
  , ≤⨆1 a1 a-inc1 i
  where
  a0 : ℕ → A⊥0
  a0 i = a i .proj₁
  a1 : ∀ i → A⊥1 (a0 i)
  a1 i = a i .proj₂ 
  a-inc0 : ℕ → ≤0
  a-inc0 i = a-inc i .proj₁
  a-inc1 : ∀ i → a0 i ≤1 a0 (suc i) ⊣ a-inc0 i
  a-inc1 i = a-inc i .proj₂ 

⨆≤ : ∀ a a-inc x → (∀ i → a i ≤ x) → ⨆ a a-inc ≤ x
⨆≤ a a-inc (x0 , x1) p =
    ⨆≤0 x0 a0 a-inc0 p0
  , ⨆≤1 x1 a1 a-inc1 p1
  where
  a0 : ℕ → A⊥0
  a0 i = a i .proj₁
  a1 : ∀ i → A⊥1 (a0 i)
  a1 i = a i .proj₂ 
  a-inc0 : ℕ → ≤0
  a-inc0 i = a-inc i .proj₁
  a-inc1 : ∀ i → a0 i ≤1 a0 (suc i) ⊣ a-inc0 i
  a-inc1 i = a-inc i .proj₂ 
  p0 : ℕ → ≤0
  p0 i = p i .proj₁
  p1 : ∀ i → a0 i ≤1 x0 ⊣ p0 i
  p1 i = p i .proj₂

≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
≈antisym {(x0 , x1)} {(y0 , y1)} (p0 , p1) (q0 , q1) =
  ≈antisym0 x0 y0 p0 q0 , ≈antisym1 x1 y1 p1 q1

≈refl : ∀ {x} → x ≈ x
≈refl {x} = ≈antisym {x} {x} (≤refl {x}) (≤refl {x})

≈sym : ∀ {x y} → x ≈ y → y ≈ x
≈sym {x , x0} {y}
  (≈antisym0 _ _ p0 q0 , ≈antisym1 x1 y1 p1 q1)
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

