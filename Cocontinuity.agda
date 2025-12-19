{-# OPTIONS --type-in-type #-}
open import Prelude
open import Setoid
open import Colimit 

module Cocontinuity {ℓI} {ℓI'} {ℓ≤} -- {ℓB}
  {I : Setoid ℓI ℓI'}
  (≤p : Preorder I ℓ≤) where

open Colim ≤p
open import Data.Product

module ≤ = IsPreorder (≤p .proj₂)
_≤_ : ≈.Rel≈ I ℓ≤
_≤_ = ≤p .proj₁
open ≈.Setoid I using () renaming (Carrier to Î)
module I = ≈.Setoid I

private
  variable
    ℓF ℓF' : Level

_∘_ : ∀ {ℓF ℓF'} → (F : ≈.Functor ℓF ℓF') (P : Diagram ≤p) → Diagram ≤p
F ∘ P = record
  { D-ob = D-ob
  ; D-mor = D-mor
  ; D-id = λ {i} → D-id {i}
  ; D-comp = λ {i} {j} {k} → D-comp {i} {j} {k} }
  where
  module F = ≈.Functor F
  module P = Diagram P
  open ≈.Setoid using () renaming (_≈_ to _⊢_≈_)
  D-ob : (i : P.I.Carrier) → Setoid _ _
  D-ob = λ i → F.F-ob (P.D-ob i)
  D-mor : ∀ {i j} → ≤p .proj₁ i j
      → ≈.Hom (F.F-ob (P.D-ob i)) (F.F-ob (P.D-ob j))
  D-mor p = record
    { ⟦_⟧ = F.F-mor (P.D-mor p) .≈.Hom.⟦_⟧
    ; cong = F.F-mor (P.D-mor _) .≈.Hom.cong }
  D-id : ∀ {i} → {x y : ⟨ D-ob i ⟩}
       → D-ob i ⊢ x ≈ y
       → D-ob i ⊢ (F.F-mor (P.D-mor (≤.refl P.I.refl)) .≈.Hom.⟦_⟧ x) ≈ y
  D-id {i} {x} {y} x≈y = D-ob i .trans u (F.F-id x≈y)
    where
    open ≈.Setoid
    open ≈.Hom
    open import Equivalence
    v : ≈.Hom (F.F-ob (P.D-ob i)) (F.F-ob (P.D-ob i))
    v = F.F-mor (P.D-mor {i} {i} (≤.refl P.I.refl))
    b : ∀ x' → P.D-ob i ⊢ P.D-mor (≤.refl P.I.refl) .⟦_⟧ x'
                        ≈ ≈.idHom .⟦_⟧ x'
    b x' = P.D-id (P.D-ob i .refl)
    c : ≈.Hom≈ (F.F-mor {S = P.D-ob i} ≈.idHom) (≈.idHom)
    c = F.F-id
    d : {!!}
    u : D-ob i ⊢ (F.F-mor (P.D-mor (≤.refl P.I.refl)) .⟦_⟧ x)
               ≈ (F.F-mor ≈.idHom) .⟦_⟧ x
    u = {!!}
    x' y' : ⟨ P.D-ob i ⟩
    x' = {!!}
    x'≈y' : P.D-ob i ⊢ x' ≈ y'
    x'≈y' = {!!}
    a : P.D-ob i ⊢ (P.D-mor _ .⟦_⟧ x') ≈ y'
    a = P.D-id {i} {x'} x'≈y'
  D-comp : ∀ {i j k} → {!!}
  D-comp = {!!}

-- -- module _ (P : Diagram isPreorder B) (F : ≈.Functor) where
-- -- ϕ : Colim₀ {!F ≈.∘ P!}
