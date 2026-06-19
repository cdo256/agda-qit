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
⊥p* {ℓA} = Liftp ℓA ⊥p
⊥* : ∀ {ℓA} → Set ℓA
⊥* {ℓA} = Lift ℓA ⊥

data ⊤p : Prop where
  tt : ⊤p
⊤ : Set
⊤ = Box ⊤p
⊤p* : ∀ {ℓA} → Prop ℓA
⊤p* {ℓA} = Liftp ℓA ⊤p
⊤* : ∀ {ℓA} → Set ℓA
⊤* {ℓA} = Lift ℓA ⊤

pattern ttˢ = box tt
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

record ΣP {a b} (A : Set a) (B : A → Prop b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open ΣP public

⟨_⟩ᴾ : ∀ {a b} {A : Set a} {B : A → Prop b} → ΣP A B → A
⟨ x , _ ⟩ᴾ = x

module ⊎ where
  data _⊎_ {ℓA ℓB} (A : Set ℓA) (B : Set ℓB) : Set (ℓA ⊔ ℓB) where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B
open ⊎ using (_⊎_; inj₁; inj₂) public

data Bool : Set where
  true : Bool
  false : Bool
