{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.QIIT ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Category.Base
open import QIT.Category.Set
open import QIT.Category.Discrete 
open import QIT.Category.SetoidEnriched 
open import QIT.Functor.Base
open import QIT.Setoid

{-# NO_POSITIVITY_CHECK #-}
mutual 
  data SortSpec : Set₁ where
    ∙ˢ : SortSpec
    _▷ˢ_ : (ℋ : SortSpec)
         → Functor (Category≈→Category (BaseCategory≈ ℋ)) (SetCat ℓ0)
         → SortSpec

  BaseCategory≈ : SortSpec → Category≈ ℓ0 ℓ0 ℓ0 ℓ0
  BaseCategory≈ ∙ˢ = DiscreteCat≈ (⊤ /≡)
  BaseCategory≈ (ℋ ▷ˢ H) = record
    { Obj = {!!}
    ; _≈⁰_ = {!!}
    ; _⇒_ = {!!}
    ; _≈⃗_ = {!!}
    ; id = {!!}
    ; _∘_ = {!!}
    ; equiv⁰ = {!!}
    ; equiv⃗ = {!!}
    ; substᵒ = {!!}
    ; subst-resp-≈⃗ = {!!}
    ; subst-refl = {!!}
    ; subst-trans = {!!}
    ; assoc = {!!}
    ; sym-assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; identity² = {!!}
    ; ∘-resp-≈ = {!!}
    ; subst-idᵒ = {!!}
    ; subst-∘ = {!!}
    }
    where
    C : Category≈ ℓ0 ℓ0 ℓ0 ?
    C = BaseCategory≈ ℋ
    module C = Category≈ C
    module H = Functor H
    record C⁺-ob : Set where
      inductive
      field
        X : C.Obj
        P : H.ob X → Set
        P-subst : ∀ {Y} → {x : H.ob Y} → (f g : Y C.⇒ X)
                → f C.≈⃗ g → P (H.hom f x) → P (H.hom g x)
        _≈ᶜ_ : ∀ {x : H.ob X} (p₁ p₂ : P x) → Prop 
        P≈-resp-hom≈
          : ∀ {Y} → {x : H.ob Y} → (f g : Y C.⇒ X)
          → (p₁ : P (H.hom f x)) (p₂ : P (H.hom g x))
          → (q : f C.≈⃗ g)
          → P-subst f g q p₁ ≈ᶜ p₂
  BaseCategory : SortSpec → Category ℓ0 ℓ0 ℓ0
  BaseCategory ∙ˢ = ⊤Cat
  BaseCategory (ℋ ▷ˢ H) = record
    { Obj = C⁺-ob
    ; _⇒_ = {!C⁺-hom!}
    ; _≈_ = {!C⁺-hom≈!}
    ; id = {!!}
    ; _∘_ = {!!}
    ; assoc = {!!}
    ; sym-assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; identity² = {!!}
    ; equiv = {!!}
    ; ∘-resp-≈ = {!!}
    }
    where
    C : Category ℓ0 ℓ0 ℓ0
    C = BaseCategory ℋ
    module C = Category C
    module H = Functor H
    record C⁺-ob : Set where
      inductive
      field
        X : C.Obj
        P : H.ob X → Set
        P-subst : ∀ {Y} → {x : H.ob Y} → (f g : Y C.⇒ X)
                → f C.≈ g → P (H.hom f x) → P (H.hom g x)
        _≈ᶜ_ : ∀ {x : H.ob X} (p₁ p₂ : P x) → Prop 
        P≈-resp-hom≈
          : ∀ {Y} → {x : H.ob Y} → (f g : Y C.⇒ X)
          → (p₁ : P (H.hom f x)) (p₂ : P (H.hom g x))
          → (q : f C.≈ g)
          → P-subst f g q p₁ ≈ᶜ p₂
                
    -- C⁺-hom : C⁺-ob → C⁺-ob → Set
    -- C⁺-hom A B =
    --   Σ (A.X C.⇒ B.X) λ f → ∀ x → P x → Q (H.hom f x)
    --   where
    --   module A = C⁺-ob A
    --   module B = C⁺-ob B
    -- -- C⁺-hom≈ : ∀ {A B} → C⁺-hom A B → C⁺-hom A B → Prop
    -- -- C⁺-hom≈ {X , P ∶ _} {Y , Q ∶ Q-subst} (f₁ , g₁) (f₂ , g₂) =
    -- --     (f₁ C.≈ f₂)
    -- --   ∧ᵖ λ f≈ → (∀ x → (p : P x)
    -- --           → let a = Q-subst f₁ f₂ f≈ (g₁ x p)
    -- --                 b = (g₂ x p) in {!!} )
