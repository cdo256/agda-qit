{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid
open import Data.Product

module QIT.Diagram {ℓI} {ℓ≤} {ℓB} {ℓB'}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  where

module ≤ = IsPreorder (≤p .proj₂)
_≤_ : BinaryRel I ℓ≤
_≤_ = ≤p .proj₁

record Diagram : Set (ℓ≤ ⊔ lsuc ℓB ⊔ lsuc ℓB') where
  field
    D-ob : ∀ (i : I) → Setoid ℓB ℓB'
    D-mor : ∀ {i j} → (p : i ≤ j) → ≈.Hom (D-ob i) (D-ob j)
    D-id : ∀ {i : I}
         → ≈.Hom≈ (D-mor (≤.refl))
                  (≈.idHom {S = D-ob i})
    D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
           → ≈.Hom≈ (D-mor (≤.trans p q))
                    (D-mor q ≈.∘ D-mor p)

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
    { to = F.F-mor (P.D-mor p) .≈.Hom.to
    ; cong = F.F-mor (P.D-mor _) .≈.Hom.cong }
  D-id : ∀ {i} → {x y : ⟨ D-ob i ⟩}
       → D-ob i ⊢ x ≈ y
       → D-ob i ⊢ (F.F-mor (P.D-mor ≤.refl) .≈.Hom.to x) ≈ y
  D-id {i} {x} {y} x≈y = D-ob i .trans u (F.F-id x≈y)
    where
    open ≈.Setoid
    open ≈.Hom
    open import QIT.Relation.Binary
    u : D-ob i ⊢ (F.F-mor (P.D-mor ≤.refl ) .to x)
               ≈ (F.F-mor ≈.idHom) .to x
    u = F.F-resp (P.D-mor _) ≈.idHom P.D-id (F.F-ob (P.D-ob i) .refl)
  D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
         → ≈.Hom≈ (D-mor (≤.trans p q)) (D-mor q ≈.∘ D-mor p)
  D-comp {i} {j} {k} p q {x} {y} x≈y =
    begin
      to (D-mor (≤.trans p q)) x
        ≈⟨ D-ob _ .refl ⟩
      to (F.F-mor (P.D-mor (≤.trans p q))) x
        ≈⟨ F.F-resp (P.D-mor _) (P.D-mor _ ≈.∘ P.D-mor _)
                    (P.D-comp p q) (D-ob _ .refl) ⟩
      to (F.F-mor (P.D-mor q ≈.∘ P.D-mor p )) x
        ≈⟨ F.F-comp _ _ x≈y ⟩
      to (F.F-mor (P.D-mor q) ≈.∘ F.F-mor (P.D-mor p)) y
        ≈⟨ D-ob _ .refl ⟩
      to (D-mor q ≈.∘ D-mor p) y ∎
    where
    open ≈.≈syntax {S = D-ob k}
    open ≈.Setoid
    open ≈.Hom
    open import QIT.Relation.Binary
