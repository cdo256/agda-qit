open import QIT.Prelude
open import QIT.Category.Base
open import QIT.Functor.Base
open import QIT.Setoid.Base

module QIT.Functor.Composition where

-- Functor composition with diagrams: F ∘ P applies functor F to diagram P.
-- If P : I → Setoid and F : Setoid → Setoid, then F ∘ P : I → Setoid.
-- This lets us transform entire diagrams by applying functors pointwise.
_∘_ : ∀ {ℓAo ℓAh ℓAe ℓBo ℓBh ℓBe ℓCo ℓCh ℓCe}
     → {A : Category ℓAo ℓAh ℓAe}
     → {B : Category ℓBo ℓBh ℓBe}
     → {C : Category ℓCo ℓCh ℓCe}
     → (G : Functor B C) (F : Functor A B)
     → Functor A C
_∘_ {A = A} {B} {C} G F = record
  { ob = λ x → G.ob (F.ob x)
  ; hom = λ f → G.hom (F.hom f)
  ; id = id
  ; comp = comp
  ; resp = λ p → G.resp (F.resp p) }
  where
  module A = Category A
  module B = Category B
  module C = Category C
  module F = Functor F
  module G = Functor G

  id : ∀ {x : A.Obj} → G.hom (F.hom (A.id {x})) C.≈ C.id
  id = begin
    G.hom (F.hom A.id)
      ≈⟨ G.resp F.id ⟩
    G.hom B.id
      ≈⟨ G.id ⟩
    C.id ∎
    where open ≈syntax {S = C.hom-setoid}
    
  comp : ∀ {x y z : A.Obj} (f : A [ x , y ]) (g : A [ y , z ])
       → G.hom (F.hom (g A.∘ f)) C.≈ G.hom (F.hom g) C.∘ G.hom (F.hom f)
  comp f g = begin
    G.hom (F.hom (g A.∘ f))
      ≈⟨ G.resp (F.comp f g) ⟩
    G.hom (F.hom g B.∘ F.hom f)
      ≈⟨ G.comp (F.hom f) (F.hom g) ⟩
    G.hom (F.hom g) C.∘ G.hom (F.hom f) ∎
    where open ≈syntax {S = C.hom-setoid}
