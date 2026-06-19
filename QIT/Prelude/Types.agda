module QIT.Prelude.Types where

open import QIT.Prelude.Universe
open import QIT.Prelude.Truncation

private
  variable
    ℓA ℓB ℓC ℓD ℓE ℓI ℓP ℓQ ℓX ℓY ℓZ : Level

record Box {ℓA} (A : Prop ℓA) : Set ℓA where
  constructor box
  field unbox : A

open Box public

data ⊥p : Prop where
⊥ : Set
⊥ = Box ⊥p
⊥p* : ∀ {ℓA} → Prop ℓA
⊥p* {ℓA} = LiftP ℓA ⊥p
⊥* : ∀ {ℓA} → Set ℓA
⊥* {ℓA} = Lift ℓA ⊥

data ⊤p : Prop where
  tt : ⊤p
data ⊤ : Set where
  tt : ⊤
⊤p* : ∀ {ℓA} → Prop ℓA
⊤p* {ℓA} = LiftP ℓA ⊤p
⊤* : ∀ {ℓA} → Set ℓA
⊤* {ℓA} = Lift ℓA ⊤

pattern tt* = liftp tt
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

_×_ : ∀ {ℓA ℓB} (A : Set ℓA) (B : Set ℓB) → Set (ℓA ⊔ ℓB)
A × B = Σ A λ _ → B

record ΣP {ℓA ℓB} (A : Set ℓA) (B : A → Prop ℓB) : Set (ℓA ⊔ ℓB) where
  constructor _,_
  field
    fst : A
    snd : B fst

open ΣP public

⟨_⟩ᴾ : ∀ {ℓA ℓB} {A : Set ℓA} {B : A → Prop ℓB} → ΣP A B → A
⟨ x , _ ⟩ᴾ = x

module ⊎ where
  data _⊎_ {ℓA ℓB} (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B
  [_,_] : ∀ {ℓA ℓB ℓC} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC}
        → (A → C) → (B → C) → A ⊎ B → C
  [ f , g ] (inj₁ x) = f x
  [ f , g ] (inj₂ x) = g x

open ⊎ using (_⊎_; inj₁; inj₂) public

data Bool : Set where
  true : Bool
  false : Bool
