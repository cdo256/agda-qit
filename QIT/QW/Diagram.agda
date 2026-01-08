open import QIT.Prelude
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid
open import Data.Product

module QIT.QW.Diagram {ℓI} {ℓ≤}
  {I : Set ℓI}
  (≤p : Preorder I ℓ≤)
  where

module ≤ = IsPreorder (≤p .proj₂)
_≤_ : BinaryRel I ℓ≤
_≤_ = ≤p .proj₁

record Diagram ℓD ℓD' : Set (ℓ≤ ⊔ ℓI ⊔ lsuc ℓD ⊔ lsuc ℓD') where
  field
    D-ob : ∀ (i : I) → Setoid ℓD ℓD'
    D-mor : ∀ {i j} → (p : i ≤ j) → ≈.Hom (D-ob i) (D-ob j)
    D-id : ∀ {i : I}
         → D-mor (≤.refl) ≈h (≈.idHom {S = D-ob i})
    D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
           → D-mor (≤.trans p q) ≈h (D-mor q ≈.∘ D-mor p)

 
_∘_ : ∀ {ℓD ℓD' ℓF ℓF'} → (F : ≈.Functor ℓD ℓD' ℓF ℓF') (P : Diagram ℓD ℓD')
    → Diagram ℓF ℓF'
_∘_ {ℓD} {ℓD'} {ℓF} {ℓF'} F P = record
  { D-ob = D-ob
  ; D-mor = D-mor
  ; D-id = λ {i} → D-id {i}
  ; D-comp = λ {i} {j} {k} → D-comp {i} {j} {k} }
  where
  module F = ≈.Functor F
  module P = Diagram P
  open ≈.Setoid using () renaming (_≈_ to _⊢_≈_)
  D-ob : (i : I) → Setoid ℓF ℓF'
  D-ob = λ i → F.F-ob (P.D-ob i)
  D-mor : ∀ {i j} → ≤p .proj₁ i j
      → ≈.Hom (F.F-ob (P.D-ob i)) (F.F-ob (P.D-ob j))
  D-mor p = record
    { to = F.F-mor (P.D-mor p) .≈.Hom.to
    ; cong = F.F-mor (P.D-mor _) .≈.Hom.cong }
  D-id : ∀ {i} → {x y : ⟨ D-ob i ⟩}
       → D-ob i ⊢ x ≈ y
       → D-ob i ⊢ F.F-mor (P.D-mor ≤.refl) .≈.Hom.to x ≈ y
  D-id {i} {x} {y} x≈y = D-ob i .trans u (F.F-id x≈y)
    where
    open ≈.Setoid
    open ≈.Hom
    open import QIT.Relation.Binary
    u : D-ob i ⊢ (F.F-mor (P.D-mor ≤.refl ) .to x)
               ≈ (F.F-mor ≈.idHom) .to x
    u = F.F-resp (P.D-mor _) ≈.idHom P.D-id (F.F-ob (P.D-ob i) .refl)
  D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
         → D-mor (≤.trans p q) ≈h (D-mor q ≈.∘ D-mor p)
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
