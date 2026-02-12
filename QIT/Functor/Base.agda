open import QIT.Prelude
open import QIT.Category.Base

module QIT.Functor.Base
  {ℓCo} {ℓCh} {ℓCe} {ℓDo} {ℓDh} {ℓDe}
  (C : Category ℓCo ℓCh ℓCe)
  (D : Category ℓDo ℓDh ℓDe)
  where

record Functor : Set (ℓCo ⊔ ℓCh ⊔ ℓCe ⊔ ℓDo ⊔ ℓDh ⊔ ℓDe) where
  module C = Category C
  module D = Category D
  field
    ob : ∀ (x : C.Obj) → D.Obj
    hom : ∀ {x y : C.Obj} → C [ x , y ] → D [ ob x , ob y ]
    id : ∀ {x : C.Obj} → hom C.id D.≈ D.id {ob x}
    comp : ∀ {x y z : C.Obj} → (f : C [ x , y ]) → (g : C [ y , z ])
         → hom (g C.∘ f) D.≈ (hom g D.∘ hom f)
    resp : ∀ {x y} {f g : C [ x , y ]} → C [ f ≈ g ] → D [ hom f ≈ hom g ] 

