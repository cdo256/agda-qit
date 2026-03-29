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

≈proj1 : ∀ {x y} → x ≈ y → x ≤ y
≈proj1 (≈antisym0 _ _ p0 q0 , ≈antisym1 _ _ p1 q1) = p0 , p1
≈proj2 : ∀ {x y} → x ≈ y → y ≤ x
≈proj2 (≈antisym0 _ _ p0 q0 , ≈antisym1 _ _ p1 q1) = q0 , q1


≈refl : ∀ {x} → x ≈ x
≈refl {x} = ≈antisym {x} {x} (≤refl {x}) (≤refl {x})

≈sym : ∀ {x y} → x ≈ y → y ≈ x
≈sym {x} {y} x≈y = ≈antisym {y} {x} y≤x x≤y
  where
  x≤y = ≈proj1 {x} {y} x≈y
  y≤x = ≈proj2 {x} {y} x≈y

≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈trans {x} {y} {z} x≈y y≈z =
  ≈antisym {x} {z} (≤trans {x} {y} {z} x≤y y≤z)
                   (≤trans {z} {y} {x} z≤y y≤x)
  where
  x≤y = ≈proj1 {x} {y} x≈y
  y≤x = ≈proj2 {x} {y} x≈y
  y≤z = ≈proj1 {y} {z} y≈z
  z≤y = ≈proj2 {y} {z} y≈z

≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
≤cong {x} {x'} {y} {y'} x≈x' y≈y' x≤y =
  ≤trans {x'} {x} {y'} x'≤x (≤trans {x} {y} {y'} x≤y y≤y')
  where
  x≤x' = ≈proj1 {x} {x'} x≈x'
  x'≤x = ≈proj2 {x} {x'} x≈x'
  y≤y' = ≈proj1 {y} {y'} y≈y'
  y'≤y = ≈proj2 {y} {y'} y≈y'

≤cong⨆ : {a b : ℕ → A⊥}
        → {a-inc : ∀ i → a i ≤ a (suc i)}
        → {b-inc : ∀ i → b i ≤ b (suc i)}
        → (p : ∀ i → a i ≤ b i)
        → ⨆ a a-inc ≤ ⨆ b b-inc
≤cong⨆ {a} {b} {a-inc} {b-inc} p =
  ⨆≤ a a-inc (⨆ b b-inc)
    (λ i → ≤trans {a i} {b i} {⨆ b b-inc} (p i) (≤⨆ b b-inc i))

≈cong⨆ : {a b : ℕ → A⊥}
        → {a-inc : ∀ i → a i ≤ a (suc i)}
        → {b-inc : ∀ i → b i ≤ b (suc i)}
        → (p : ∀ i → a i ≈ b i)
        → ⨆ a a-inc ≈ ⨆ b b-inc
≈cong⨆ {a} {b} {a-inc} {b-inc} p =
  ≈antisym
    {⨆ a a-inc} {⨆ b b-inc}
    (≤cong⨆ {a} {b} {a-inc} {b-inc} λ i → ≈proj1 {a i} {b i} (p i))
    (≤cong⨆ {b} {a} {b-inc} {a-inc} λ i → ≈proj2 {a i} {b i} (p i))
