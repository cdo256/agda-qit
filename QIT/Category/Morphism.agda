open import QIT.Prelude
open import QIT.Category.Base

module QIT.Category.Morphism
       {ℓCo} {ℓCh} {ℓCe}
       (C : Category ℓCo ℓCh ℓCe)
       where
  open Category C

  record IsIso {x y} (f : C [ x , y ]) : Set (ℓCh ⊔ ℓCe) where
    field
      g : C [ y , x ]
      linv : g ∘ f ≈ id
      rinv : f ∘ g ≈ id

  IsMonic : ∀ {x y} (f : C [ x , y ]) → Prop (ℓCo ⊔ ℓCh ⊔ ℓCe) 
  IsMonic {x} {y} f = ∀ z (g h : C [ z , x ]) → (f ∘ g) ≈ (f ∘ h) → g ≈ h 

  IsEpic : ∀ {x y} (f : C [ x , y ]) → Prop (ℓCo ⊔ ℓCh ⊔ ℓCe) 
  IsEpic {x} {y} f = ∀ z (g h : C [ y , z ]) → (g ∘ f) ≈ (h ∘ f) → g ≈ h 
