open import QIT.Prelude
open import QIT.Category.Base
open import QIT.Functor.Base
open import QIT.Category.Morphism

module QIT.NatTrans
  {ℓCo} {ℓCh} {ℓCe} {ℓDo} {ℓDh} {ℓDe}
  {C : Category ℓCo ℓCh ℓCe}
  {D : Category ℓDo ℓDh ℓDe}
  (F : Functor C D)
  (G : Functor C D)
  where

record NatTrans : Set (ℓCo ⊔ ℓCh ⊔ ℓCe ⊔ ℓDo ⊔ ℓDh ⊔ ℓDe) where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  field
    ob : ∀ (x : C.Obj) → D [ F.ob x , G.ob x ]
    hom : ∀ {x y : C.Obj} → (f : C [ x , y ])
        → (G.hom f D.∘ ob x) D.≈ (ob y D.∘ F.hom f)

record NatIso : Set (ℓCo ⊔ ℓCh ⊔ ℓCe ⊔ ℓDo ⊔ ℓDh ⊔ ℓDe) where
  module C = Category C
  module D = Category D
  module F = Functor F
  module G = Functor G
  field
    ob : ∀ (x : C.Obj) → D [ F.ob x , G.ob x ]
    hom : ∀ {x y : C.Obj} → (f : C [ x , y ])
        → (G.hom f D.∘ ob x) D.≈ (ob y D.∘ F.hom f)
    isIso : ∀ x → IsIso D (ob x)
