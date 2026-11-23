{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient

-- Fiore--Pitts--Steenkamp's stages obtained by iterating the free term monad.
module QIT.QW.Stage.IteratedMonad
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (Zᴬ : PlumpAlgebra (sig .Sig.S) (sig .Sig.P))
  where

open Sig sig
module Z = PlumpAlgebra Zᴬ
open import QIT.Plump.Properties Zᴬ
open import QIT.QW.Equation S P ℓV

Size = Z.Z

Πᵇ : ∀ {ℓB}
  → (i : Size)
  → (B : ∀ j → j Z.< i → Set ℓB)
  → Set ℓB
Πᵇ i B = ∀ j j<i → B j j<i

Σᵇ : ∀ {ℓB}
  → (i : Size)
  → (B : ∀ j → j Z.< i → Set ℓB)
  → Set ℓB
Σᵇ i B = Σ (↓ i) λ (j , j<i) → B j j<i

∀ᵇ : ∀ {ℓB}
  → (i : Size)
  → (B : ∀ j → j Z.< i → Prop ℓB)
  → Prop ℓB
∀ᵇ i B = ∀ j j<i → B j j<i

Dᵇ-type : (i : Size) → Set _
Dᵇ-type i = Πᵇ i λ _ _ → Set ℓV

τᵇ-type : (i : Size) → Dᵇ-type i → Set _
τᵇ-type i Dᵇ =
  Πᵇ i λ j j<i →
  Πᵇ j λ k k<j →
  Expr (Dᵇ k (Z.<< j<i k<j)) → Dᵇ j j<i

record IdxStruct : Set _ where
  constructor mkIdxStruct
  field
    D : Size → Set ℓV
    τ : ∀ i → Πᵇ i λ j _ → Expr (D j) → D i
open IdxStruct public

record IdxStructᵇ (i : Size) : Set _ where
  constructor mkIdxStructᵇ
  field
    Dᵇ : Dᵇ-type i
    τᵇ : τᵇ-type i Dᵇ
open IdxStructᵇ public

infixl 6 _↓_ _↓ᵇ_

_↓_ : IdxStruct → ∀ i → IdxStructᵇ i
(A ↓ i) .Dᵇ j _ = A .D j
(A ↓ i) .τᵇ j _ k k<j t = A .τ j k k<j t

_↓ᵇ_ : {i : Size} → IdxStructᵇ i → ∀ j → j Z.< i → IdxStructᵇ j
((A ↓ᵇ j) j<i) .Dᵇ k k<j = A .Dᵇ k (Z.<< j<i k<j)
((A ↓ᵇ j) j<i) .τᵇ k k<j = A .τᵇ k (Z.<< j<i k<j)

-- Raw inputs to stage i are terms over any strictly earlier stage.
Wᵇ : ∀ {i} → IdxStructᵇ i → Set _
Wᵇ {i} A = Σᵇ i λ j j<i → Expr (Dᵇ A j j<i)

-- Equations, monad units, and monad multiplication generate the stage quotient.
data Rᵇ {i : Size} (A : IdxStructᵇ i) : Wᵇ A → Wᵇ A → Prop _ where
  τεᵇ : ∀ j j<i
    → (e : E)
    → (ρ : Ξ e .Equation.V → Dᵇ A j j<i)
    → Rᵇ A ((j , j<i) , ExprMap ρ (Ξ e .Equation.lhs))
           ((j , j<i) , ExprMap ρ (Ξ e .Equation.rhs))
  τηᵇ : ∀ j j<i k k<j
    → (t : Expr (Dᵇ A k (Z.<< j<i k<j)))
    → Rᵇ A ((j , j<i) , varᴱ (τᵇ A j j<i k k<j t))
           ((k , Z.<< j<i k<j) , t)
  τσᵇ : ∀ j j<i k k<j
    → (s : S)
    → (f : P s → Expr (Dᵇ A k (Z.<< j<i k<j)))
    → Rᵇ A ((k , Z.<< j<i k<j) , supᴱ s f)
           ((j , j<i) , supᴱ s λ p → varᴱ (τᵇ A j j<i k k<j (f p)))

-- The next iterated-monad stage (FPS (6.1)).
◇ : ∀ {i} → IdxStructᵇ i → Set _
◇ A = Wᵇ A / Rᵇ A

-- A fixed structure identifies every stage with the quotient generated below it.
record FixedPoint (A : IdxStruct) : Set _ where
  field
    stage : ∀ i → D A i ≅ˢ ◇ (A ↓ i)
    τ-β : ∀ i j j<i (t : Expr (D A j))
      → _≅ˢ_.to (stage i) (τ A i j j<i t)
      ≡ Q.[ ((j , j<i) , t) ]
open FixedPoint public

◇fix : IdxStruct → Set _
◇fix = FixedPoint

FixSizeStruct : Set _
FixSizeStruct = Σ IdxStruct FixedPoint
