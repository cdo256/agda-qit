module QIT.Setoid.Functor where

open import QIT.Prelude
open import QIT.Setoid.Base
open import QIT.Setoid.Hom

record Functor ℓd ℓd' ℓc ℓc' : Set (lsuc ℓd ⊔ lsuc ℓd' ⊔ lsuc ℓc ⊔ lsuc ℓc') where
  private
    D = Setoid ℓd ℓd'
  field
    F-ob : ∀ (S : D) → Setoid ℓc ℓc'
    F-mor : ∀ {S T : D} → Hom S T → Hom (F-ob S) (F-ob T)
    F-id : ∀ {S : D} → F-mor idHom ≈h idHom {S = F-ob S}
    F-comp : ∀ {S T U : D} → (f : Hom S T) → (g : Hom T U)
           → F-mor (g ∘ f) ≈h (F-mor g ∘ F-mor f)
    F-resp : ∀ {S T} (f g : Hom S T) → f ≈h g → F-mor f ≈h F-mor g
