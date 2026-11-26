{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient

-- Fiore--Pitts--Steenkamp's stages obtained by iterating the free term monad.
module QIT.QW.Stage.FixedPoint
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
open import QIT.Plump.Size
open import QIT.QW.Equation S P ℓV

Size = Z.Z

sizeStr : SizeStr Size
sizeStr = plumpSizeStr Zᴬ

open SizedTypes sizeStr public

Dᵇ-type : (i : Size) → Set _
Dᵇ-type i = Πᵇ i λ _ → Set ℓV

τᵇ-type : (i : Size) → Dᵇ-type i → Set _
τᵇ-type i Dᵇ =
  Πᵇ i λ j {j<i} →
  Πᵇ j λ k {k<j} →
  Expr (Dᵇ k {<ᵇ<ᵇ j<i k<j}) → Dᵇ j {j<i}

record IdxStruct : Set _ where
  constructor mkIdxStruct
  field
    D : Size → Set ℓV
    τ : ∀ i → Πᵇ i λ j → Expr (D j) → D i
open IdxStruct public

record IdxStructᵇ (i : Size) : Set _ where
  constructor mkIdxStructᵇ
  field
    Dᵇ : Dᵇ-type i
    τᵇ : τᵇ-type i Dᵇ
open IdxStructᵇ public

infixl 6 _↓_ _↓ᵇ_

_↓_ : IdxStruct → ∀ i → IdxStructᵇ i
(A ↓ i) .Dᵇ j = A .D j
(A ↓ i) .τᵇ j k {k<j} t = A .τ j k {k<j} t

_↓ᵇ_ : {i : Size} → IdxStructᵇ i → ∀ j {j<i : j <ᵇ i} → IdxStructᵇ j
((A ↓ᵇ j) {j<i}) .Dᵇ k {k<j} = A .Dᵇ k {<ᵇ<ᵇ j<i k<j}
((A ↓ᵇ j) {j<i}) .τᵇ k {k<j} = A .τᵇ k {<ᵇ<ᵇ j<i k<j}

-- Raw inputs to stage i are terms over any strictly earlier stage.
Wᵇ : ∀ {i} → IdxStructᵇ i → Set _
Wᵇ {i} A = Σᵇ i λ j {j<i} → Expr (Dᵇ A j {j<i})

-- Equations, monad units, and monad multiplication generate the stage quotient.
data Rᵇ {i : Size} (A : IdxStructᵇ i) : Wᵇ A → Wᵇ A → Prop _ where
  τεᵇ : ∀ᵇ i λ j {j<i} →
    (e : E)
    → (ρ : Ξ e .Equation.V → Dᵇ A j {j<i})
    → Rᵇ A (pairᵇ j (ExprMap ρ (Ξ e .Equation.lhs)))
           (pairᵇ j (ExprMap ρ (Ξ e .Equation.rhs)))
  τηᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
    (t : Expr (Dᵇ A k {<ᵇ<ᵇ j<i k<j}))
    → Rᵇ A (pairᵇ j (varᴱ (τᵇ A j {j<i} k {k<j} t)))
           (pairᵇ k {<ᵇ<ᵇ j<i k<j} t)
  τσᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
    (s : S)
    → (f : P s → Expr (Dᵇ A k {<ᵇ<ᵇ j<i k<j}))
    → Rᵇ A (pairᵇ k {<ᵇ<ᵇ j<i k<j} (supᴱ s f))
           (pairᵇ j (supᴱ s λ p → varᴱ (τᵇ A j {j<i} k {k<j} (f p))))

-- The next iterated-monad stage (FPS (6.1)).
◇ : ∀ {i} → IdxStructᵇ i → Set _
◇ A = Wᵇ A / Rᵇ A

-- A fixed structure identifies every stage with the quotient generated below it.
record FixedPoint (A : IdxStruct) : Set _ where
  field
    stage : ∀ i → D A i ≅ˢ ◇ (A ↓ i)
    τ-β : ∀ i j {j<i} (t : Expr (D A j))
      → stage i .≅ˢ.to  (τ A i j {j<i} t)
      ≡ Q.[ pairᵇ j {j<i} t ]
open FixedPoint public

◇fix : IdxStruct → Set _
◇fix = FixedPoint

FixSizeStruct : Set _
FixSizeStruct = Σ IdxStruct FixedPoint
