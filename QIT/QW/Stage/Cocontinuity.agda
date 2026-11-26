{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient

module QIT.QW.Stage.Cocontinuity
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
-- module Z = PlumpAlgebra Zᴬ

open import QIT.Plump.Properties Zᴬ
open import QIT.Plump.Size
open import QIT.QW.Equation S P ℓV
open import QIT.QW.Stage.IteratedDiagram sig Zᴬ
open import QIT.QW.Stage.FixedPoint sig Zᴬ

module Bounded (α : Z.Z) where
  open import QIT.Colimit Z.<wp _
  open FromFixedPoint {!!}
  _ : Colim/ {!D!} ≅ˢ {!!}
