{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.Relation.Binary
open import QIT.Relation.SetQuotient

-- The strict size-indexed diagram associated to an iterated-monad fixed point.
module QIT.QW.Stage.IteratedMonad.Diagram
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
module Ord = PlumpAlgebra Zᴬ
open import QIT.QW.Equation S P ℓV
open import QIT.QW.Stage.IteratedMonad sig Zᴬ hiding (D)

<wp : WeakPreorder Size _
<wp = Ord._<_ , record { trans = λ p q → Ord.<< q p }

open import QIT.SimpleDiagram <wp

private
  iso-injective : ∀ {A : Set ℓV} {B : Set _} (e : A ≅ˢ B) {x y}
    → _≅ˢ_.to e x ≡ _≅ˢ_.to e y → x ≡ y
  iso-injective e p =
    ≡.trans (≡.sym (_≅ˢ_.rinv e _))
      (≡.trans (≡.cong (_≅ˢ_.from e) p) (_≅ˢ_.rinv e _))

module FromFixedPoint (A : IdxStruct) (fixed : FixedPoint A) where
  D′ : ∀ i j → j Ord.< i → IdxStruct.D A j → IdxStruct.D A i
  D′ i j j<i x = τ A i j j<i (varᴱ x)

  Dact : ∀ i j (j<i : j Ord.< i) k (k<j : k Ord.< j) x
    → D′ i k (Ord.<< j<i k<j) x ≡ D′ i j j<i (D′ j k k<j x)
  Dact i j j<i k k<j x = iso-injective (FixedPoint.stage fixed i) proof
    where
    proof : _≅ˢ_.to (FixedPoint.stage fixed i) (D′ i k (Ord.<< j<i k<j) x)
          ≡ _≅ˢ_.to (FixedPoint.stage fixed i) (D′ i j j<i (D′ j k k<j x))
    proof = ≡.trans (FixedPoint.τ-β fixed i k (Ord.<< j<i k<j) (varᴱ x))
      (≡.trans
        (≡.sym (Q.quot-rel _ _ (τηᵇ j j<i k k<j (varᴱ x))))
        (≡.sym (FixedPoint.τ-β fixed i j j<i (varᴱ (D′ j k k<j x)))))

  D : Diagram ℓV
  D = record
    { ob = IdxStruct.D A
    ; edge = λ {i} {j} i<j → D′ j i i<j
    ; nat = λ {i} {j} {k} i<j j<k → Dact k j j<k i i<j }

  open import QIT.Colimit <wp ℓV D

  D* = Colim
  D*/ = Colim/
