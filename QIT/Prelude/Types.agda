module QIT.Prelude.Types where

open import QIT.Prelude.Universe
open import QIT.Prelude.Truncation

record Box (A : Prop ℓA) : Set ℓA where
  constructor box
  field unbox : A

open Box public

data ⊥ˢ : Set where
⊥ˢ* : Set ℓA
⊥ˢ* = Lift _ ⊥ˢ

data ⊤ˢ : Set where
  tt : ⊤ˢ
⊤ˢ* : Set ℓA
⊤ˢ* = Lift _ ⊤ˢ

pattern tt* = lift tt

infixr 4 _,_

open import Agda.Builtin.Sigma public
  renaming (fst to proj₁; snd to proj₂)
  hiding (module Σ)

module Σ = Agda.Builtin.Sigma.Σ
  renaming (fst to proj₁; snd to proj₂)

open Σ public
{-# DISPLAY Agda.Builtin.Sigma.Σ.fst = proj₁ #-}
{-# DISPLAY Agda.Builtin.Sigma.Σ.snd = proj₂ #-}

_×_ : (A : Set ℓA) (B : Set ℓB) → Set (ℓA ⊔ ℓB)
A × B = Σ A λ _ → B

record ΣP (A : Set ℓA) (B : A → Prop ℓB) : Set (ℓA ⊔ ℓB) where
  constructor _,_
  field
    fst : A
    snd : B fst

open ΣP public

⟨_⟩ᴾ : {A : Set ℓA} {B : A → Prop ℓB} → ΣP A B → A
⟨ x , _ ⟩ᴾ = x

module ⊎ where
  data _⊎_ (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B
  [_,_] : {A : Set ℓA} {B : Set ℓB} {C : A ⊎ B → Set ℓC}
        → ((a : A) → C (inj₁ a))
        → ((b : B) → C (inj₂ b))
        → (x : A ⊎ B) → C x
  [ f , g ] (inj₁ x) = f x
  [ f , g ] (inj₂ x) = g x
  [_,_]ᵖ : {A : Set ℓA} {B : Set ℓB} {C : A ⊎ B → Prop ℓC}
        → ((a : A) → C (inj₁ a))
        → ((b : B) → C (inj₂ b))
        → (x : A ⊎ B) → C x
  [ f , g ]ᵖ (inj₁ x) = f x
  [ f , g ]ᵖ (inj₂ x) = g x

open ⊎ using (_⊎_; inj₁; inj₂) public

data Bool : Set where
  true : Bool
  false : Bool
