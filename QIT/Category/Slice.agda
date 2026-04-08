module QIT.Category.Slice where

open import QIT.Prelude
open import QIT.Relation.Subset
open import QIT.Category.Base

module _ {ℓCo ℓCh ℓCe} (C : Category ℓCo ℓCh ℓCe) where
  open Category C

  Slice : Obj → Category (ℓCo ⊔ ℓCh) (ℓCh ⊔ ℓCe) ℓCe
  Slice x = record
    { Obj = Σ Obj (_⇒ x)
    ; _⇒_ = λ (y , f) (z , g) → ΣP (y ⇒ z) (λ h → (g ∘ h) ≈ f)
    ; _≈_ =  λ (f , _) (g , _) → f ≈ g
    ; id = λ {(y , f)} → id , identityʳ
    ; _∘_ = λ { (h , ph) (g , pg) → (h ∘ g) , trans sym-assoc (trans (∘-resp-≈ˡ ph) pg) }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv = record
      { refl = refl
      ; sym = sym
      ; trans = trans }
    ; ∘-resp-≈ = ∘-resp-≈
    }

  CoSlice : Obj → Category (ℓCo ⊔ ℓCh) (ℓCh ⊔ ℓCe) ℓCe
  CoSlice x = record
    { Obj = Σ Obj (x ⇒_)
    ; _⇒_ = λ (y , f) (z , g) → ΣP (y ⇒ z) (λ h → (h ∘ f) ≈ g)
    ; _≈_ = λ (f , _) (g , _) → f ≈ g
    ; id = λ {(y , f)} → id , identityˡ
    ; _∘_ = λ { (h , ph) (g , pg) → (h ∘ g) , trans assoc (trans (∘-resp-≈ʳ pg) ph) }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv = record
      { refl = refl
      ; sym = sym
      ; trans = trans }
    ; ∘-resp-≈ = ∘-resp-≈
    }
