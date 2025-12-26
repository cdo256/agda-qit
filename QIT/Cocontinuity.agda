{-# OPTIONS --type-in-type #-}
open import QIT.Prelude
open import QIT.Setoid
import QIT.Colimit as Colimit
open import QIT.Relation.Base
open import QIT.Relation.Binary

module QIT.Cocontinuity {ℓI} {ℓ≤} -- {ℓB}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤) where

open Colimit ≤p
open import Data.Product

module ≤ = IsPreorder (≤p .proj₂)
_≤_ : BinaryRel I ℓ≤
_≤_ = ≤p .proj₁

private
  variable
    ℓF ℓF' : Level

_∘_ : ∀ {ℓF ℓF'} → (F : ≈.Functor ℓF ℓF') (P : Diagram) → Diagram
F ∘ P = record
  { D-ob = D-ob
  ; D-mor = D-mor
  ; D-id = λ {i} → D-id {i}
  ; D-comp = λ {i} {j} {k} → D-comp {i} {j} {k} }
  where
  module F = ≈.Functor F
  module P = Diagram P
  open ≈.Setoid using () renaming (_≈_ to _⊢_≈_)
  D-ob : (i : I) → Setoid _ _
  D-ob = λ i → F.F-ob (P.D-ob i)
  D-mor : ∀ {i j} → ≤p .proj₁ i j
      → ≈.Hom (F.F-ob (P.D-ob i)) (F.F-ob (P.D-ob j))
  D-mor p = record
    { ⟦_⟧ = F.F-mor (P.D-mor p) .≈.Hom.⟦_⟧
    ; cong = F.F-mor (P.D-mor _) .≈.Hom.cong }
  D-id : ∀ {i} → {x y : ⟨ D-ob i ⟩}
       → D-ob i ⊢ x ≈ y
       → D-ob i ⊢ (F.F-mor (P.D-mor ≤.refl) .≈.Hom.⟦_⟧ x) ≈ y
  D-id {i} {x} {y} x≈y = D-ob i .trans u (F.F-id x≈y)
    where
    open ≈.Setoid
    open ≈.Hom
    open import QIT.Relation.Binary
    u : D-ob i ⊢ (F.F-mor (P.D-mor ≤.refl ) .⟦_⟧ x)
               ≈ (F.F-mor ≈.idHom) .⟦_⟧ x
    u = F.F-resp P.D-id (F.F-ob (P.D-ob i) .refl)
  D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
         → ≈.Hom≈ (D-mor (P.≤.trans p q)) (D-mor q ≈.∘ D-mor p)
  D-comp {i} {j} {k} p q {x} {y} x≈y =
    begin
      ⟦ D-mor (P.≤.trans p q) ⟧ x
        ≈⟨ D-ob _ .refl ⟩
      ⟦ F.F-mor (P.D-mor (P.≤.trans p q)) ⟧ x
        ≈⟨ F.F-resp (P.D-comp p q) (D-ob _ .refl) ⟩
      ⟦ F.F-mor (P.D-mor q ≈.∘ P.D-mor p ) ⟧ x
        ≈⟨ F.F-comp _ _ x≈y ⟩
      ⟦ F.F-mor (P.D-mor q) ≈.∘ F.F-mor (P.D-mor p) ⟧ y
        ≈⟨ D-ob _ .refl ⟩
      ⟦ D-mor q ≈.∘ D-mor p ⟧ y ∎
    where
    open ≈.≈syntax {S = D-ob k}
    open ≈.Setoid
    open ≈.Hom
    open import QIT.Relation.Binary

Cocontinuous : ∀ {ℓF ℓF'} → (F : ≈.Functor ℓF ℓF') (P : Diagram) → Prop lzero
Cocontinuous F P = Colim.Colim (F ∘ P) ≅ F.F-ob (Colim.Colim P)
  where
  module F = ≈.Functor F
