{-# OPTIONS --allow-unsolved-metas #-}
module QIT.Examples.ConTy.IIT where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.HetPath as ≣ using (_≣_)
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

data Con : Set
data Ty : Con → Set

data Con where
  ∙ : Con
  _▷_ : (Γ : Con) → Ty Γ → Con

data Ty where
  ι : (Γ : Con) → Ty Γ
  Π̇ : (Γ : Con) → (A : Ty Γ) → (B : Ty (Γ ▷ A)) → Ty Γ
