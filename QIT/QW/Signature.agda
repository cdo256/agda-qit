{-# OPTIONS --type-in-type #-}
module QIT.QW.Signature where

open import QIT.Prelude
open import QIT.Setoid
open import QIT.QW.Equation using (Equation)
open import QIT.Container.Base

private
  variable
    ℓS ℓP ℓE ℓV : Level

record Sig ℓS ℓP ℓE ℓV : Set (lsuc ℓE ⊔ lsuc ℓV ⊔ lsuc ℓS ⊔ lsuc ℓP) where
  field
    S : Set ℓS
    P : S → Set ℓP
    E : Set ℓE
    Ξ : E → Equation S P ℓV

  open Equation public

module _ {ℓS ℓP ℓE ℓV} ℓX ℓ≈ (sig : Sig ℓS ℓP ℓE ℓV) where
  open Sig sig
  open import QIT.Container.Functor S P
  open import QIT.QW.Equation S P

  record Record : Set _ where
    field
      Xα : ≈.Algebra (F ℓX ℓ≈)
      sat : Sat Xα Ξ
      rec : ∀ Yβ → Sat Yβ Ξ → ≈.Alg.Hom (F ℓX ℓ≈) Xα Yβ
      unique : ∀ Yβ → (satY : Sat Yβ Ξ) → (f : ≈.Alg.Hom (F ℓX ℓ≈) Xα Yβ)
             → f .≈.Alg.Hom.hom ≈h rec Yβ satY .≈.Alg.Hom.hom
