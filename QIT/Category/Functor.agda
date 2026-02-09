open import QIT.Prelude
open import QIT.Category.Base

module QIT.Category.Functor
  {ℓCo} {ℓCh} {ℓCe} {ℓDo} {ℓDh} {ℓDe}
  (C : Category ℓCo ℓCh ℓCe)
  (D : Category ℓDo ℓDh ℓDe)
  where

record Functor : Set (ℓCo ⊔ ℓCh ⊔ ℓCe ⊔ ℓDo ⊔ ℓDh ⊔ ℓDe) where
  module C = Category C
  module D = Category D
  field
    ob : ∀ (S : C.Obj) → D.Obj
    hom : ∀ {S T : C.Obj} → S C.⇒ T → (ob S) D.⇒ (ob T)
    id : ∀ {S : C.Obj} → hom C.id D.≈ D.id {ob S}
    comp : ∀ {S T U : C.Obj} → (f : S C.⇒ T) → (g : T C.⇒ U)
           → hom (g C.∘ f) D.≈ (hom g D.∘ hom f)
