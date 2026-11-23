{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
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

record Diagram : Set _ where
  field
    vtx : Size → Set ℓV
    edg : ∀ i j → j Ord.< i → vtx j → vtx i
    act : ∀ i j (j<i : j Ord.< i) k (k<j : k Ord.< j) x
      → edg i k (Ord.<< j<i k<j) x ≡ edg i j j<i (edg j k k<j x)
open Diagram public

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

  D : Diagram
  D = record { vtx = IdxStruct.D A ; edg = D′ ; act = Dact }

-- The colimit relation used by FPS: two elements agree at a common later stage.
module Colimit (Dg : Diagram) where
  data _≈_ : Σ Size (vtx Dg) → Σ Size (vtx Dg) → Prop _ where
    common : ∀ {i j} {x : vtx Dg i} {y : vtx Dg j}
      → (k : Size) → (i<k : i Ord.< k) → (j<k : j Ord.< k)
      → edg Dg k i i<k x ≡ edg Dg k j j<k y
      → (i , x) ≈ (j , y)

  colim : Set _
  colim = Σ Size (vtx Dg) / _≈_

  ν : ∀ i → vtx Dg i → colim
  ν i x = Q.[ i , x ]
