{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.Relation.Binary
open import QIT.Relation.SetQuotient

-- The strict size-indexed diagram associated to an iterated-monad fixed point.
module QIT.QW.Stage.IteratedDiagram
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
open PlumpAlgebra Zᴬ
open import QIT.Plump.Size
open import QIT.QW.Equation S P ℓV
open import QIT.QW.Stage.FixedPoint sig Zᴬ hiding (D)
module Sz = SizeStr sizeStr

open import QIT.SimpleDiagram Sz.<wp

private
  iso-injective : ∀ {A : Set ℓV} {B : Set _} (e : A ≅ˢ B) {x y}
    → _≅ˢ_.to e x ≡ _≅ˢ_.to e y → x ≡ y
  iso-injective e p =
    ≡.trans (≡.sym (_≅ˢ_.rinv e _))
      (≡.trans (≡.cong (_≅ˢ_.from e) p) (_≅ˢ_.rinv e _))

module FromFixedPoint (A : IdxStruct) (fixed : FixedPoint A) where
  D' : ∀ i j → j < i → IdxStruct.D A j → IdxStruct.D A i
  D' i j j<i x = τ A i j {j<i} (varᴱ x)

  Dact : ∀ i j (j<i : j < i) k (k<j : k < j) x
    → D' i k (<< j<i k<j) x ≡ D' i j j<i (D' j k k<j x)
  Dact i j j<i k k<j x = iso-injective (FP.stage i) proof
    where
    module FP = FixedPoint fixed
    proof : ≅ˢ.to (FP.stage i) (D' i k (<< j<i k<j) x)
          ≡ ≅ˢ.to (FP.stage i) (D' i j j<i (D' j k k<j x))
    proof = ≡.trans (FP.τ-β i k {<< j<i k<j} (varᴱ x))
      (≡.trans
        (≡.sym (Q.quot-rel _ _ (τηᵇ j {j<i} k {k<j} (varᴱ x))))
        (≡.sym (FP.τ-β i j {j<i} (varᴱ (D' j k k<j x)))))

  D : Diagram ℓV
  D = record
    { ob = IdxStruct.D A
    ; edge = λ {i} {j} i<j → D' j i i<j
    ; nat = λ {i} {j} {k} i<j j<k → Dact k j j<k i i<j }

  open import QIT.Colimit Sz.<wp ℓV D

  D* = Colim
  D*/ = Colim/
