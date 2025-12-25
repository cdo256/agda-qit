{-# OPTIONS --type-in-type #-}
module QIT.Mobile.Functor (B : Set) where

open import QIT.Prelude
open import QIT.Equivalence
open import QIT.Mobile.Base B
open import QIT.Mobile.Equivalence B
open import QIT.Mobile.Colimit B
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)
open import Data.Unit
open import Data.Sum
open import QIT.Setoid
open import QIT.Equivalence
open import Data.Product
open import Data.Container hiding (refl; sym; trans)

private
  l0 : Level
  l0 = lzero
  Pos = Branch .Position

module Ob (S : Setoid l0 l0) where
  open ≈.Setoid S
  data _≈ᵇ_ : (x y : ⟦ Branch ⟧ ⟨ S ⟩) → Prop l0 where
    ≈bleaf : ∀ {f g} → (l , f) ≈ᵇ (l , g)
    ≈bperm : ∀ f → (π : B ↔ B)
           → (n , f) ≈ᵇ (n , λ b → f (π .↔.to b))
    ≈bext : ∀ {f g} → (∀ b → f b ≈ g b)
          → (n , f) ≈ᵇ (n , g)

  open _≈ᵇ_

  isReflexive : Reflexive _≈ᵇ_
  isReflexive {l , _} = ≈bleaf
  isReflexive {n , f} = ≈bext (λ b → refl)

  isSymmetric : Symmetric _≈ᵇ_
  isSymmetric ≈bleaf = ≈bleaf
  isSymmetric (≈bperm f π) = {!!}
  isSymmetric (≈bext p) = ≈bext (λ b → sym (p b))
