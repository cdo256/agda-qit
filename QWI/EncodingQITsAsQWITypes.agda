module QWI.EncodingQITsAsQWITypes where

open import QWI.IndexedPolynomialFunctorsAndEquationalSystems public

-- Set-valued identity types
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

----------------------------------------------------------------------
-- Finite multisets with swap (Example 7.5)
----------------------------------------------------------------------
module Bag (X : Set) where
  open Slice 𝟙
  open Syseq
  Σ : Sig
  Op Σ _ = 𝟙 + X
  Ar Σ _ (ι₁ _) _ = 𝟘
  Ar Σ _ (ι₂ _) _ = 𝟙
  ε : Syseq Σ
  Op (Γ ε) _ = X × X
  Ar (Γ ε) _ _ _ = 𝟙
  lhs ε _ (x , y) = σ _ ((ι₂ x) , (λ _ _ → σ _ ((ι₂ y) , (λ _ _ → η _ _))))
  rhs ε _ (x , y) = σ _ ((ι₂ y) , (λ _ _ → σ _ ((ι₂ x) , (λ _ _ → η _ _))))

----------------------------------------------------------------------
-- Length-indexed multisets (Example 7.6)
----------------------------------------------------------------------
module AbVec (X : Set) where
  open Slice ℕ
  open Syseq
  Σ : Sig
  Op Σ zero = 𝟙
  Op Σ (m +1) = X
  Ar Σ zero _ _ = 𝟘
  Ar Σ (m +1) _ n = m ≡ n
  ε : Syseq Σ
  Op (Γ ε) zero = 𝟘
  Op (Γ ε) (zero +1) = 𝟘
  Op (Γ ε) (m +1 +1) = X × X
  Ar (Γ ε) (m +1 +1) _ n = m ≡ n
  lhs ε (m +1 +1) (x , y) = σ (m +1 +1) (x , (λ {_ refl → σ (m +1) (y , (λ {_ refl → η m refl}))}))
  rhs ε (m +1 +1) (x , y) = σ (m +1 +1) (y , (λ {_ refl → σ (m +1) (x , (λ {_ refl → η m refl}))}))

----------------------------------------------------------------------
-- Unordered countably-branching trees (Example 7.7)
----------------------------------------------------------------------
{-
See QW.EncodingQITsAsQWTypes
-}

----------------------------------------------------------------------
-- W-suspensions
----------------------------------------------------------------------
{-
See QW.EncodingQITsAsQWTypes
-}

----------------------------------------------------------------------
-- W-types with reductions
----------------------------------------------------------------------
module _
  (Z : Set)
  where
  open Slice Z
  open Syseq
  module W-reductions
    (Y : Setᴵ lzero)
    (X : (z : Z) → Y z → Setᴵ lzero)
    (R : ∀ z → (y : Y z) → X z y z)
    where
    Σ : Sig
    Op Σ = Y
    Ar Σ = X

    ε : Syseq Σ
    Op (Γ ε) = Y
    Ar (Γ ε) = X
    lhs ε z y = σ z (y , η)
    rhs ε z y = η z (R z y)

----------------------------------------------------------------------
-- F-type
----------------------------------------------------------------------
{-
See QW.EncodingQITsAsQWTypes
-}
