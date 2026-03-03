{-# OPTIONS --type-in-type #-}
module QIT.QIIT.Attempt1 where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Binary
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
         → Functor (BaseCategory ℋ) (SetCat ℓ0)
         → SortSpec

  BaseCategory : SortSpec → Category ℓ0 ℓ0 ℓ0
  BaseCategory ∙ˢ = ⊤Cat
  BaseCategory (ℋ ▷ˢ H) = record
    { Obj = C⁺-ob
    ; _⇒_ = C⁺-hom
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
        _≈ʰ_ : ∀ {x : H.ob X} → P x → P x → Prop
        equivₓ : ∀ {x} → IsEquivalence (_≈ʰ_ {x})
        subst-resp : ∀ {x y} (e : x ≡ y) (p q : P x)
                  → p ≈ʰ q → (subst P e p) ≈ʰ (subst P e q)    
      _≈ᵖ_ : ∀ {x y : H.ob X} → P x → P y → Prop
      x ≈ᵖ x₁ = {!!}

    C⁺-hom : C⁺-ob → C⁺-ob → Set
    C⁺-hom A B =
      Σ (A.X C.⇒ B.X) λ f → ∀ x → A.P x → B.P (H.hom f x)
      where
      module A = C⁺-ob A
      module B = C⁺-ob B
    C⁺-hom≈ : ∀ {A B} → C⁺-hom A B → C⁺-hom A B → Prop
    C⁺-hom≈ {A} {B} (f₁ , g₁) (f₂ , g₂) =
        (f₁ C.≈ f₂)
      ∧ᵖ λ f≈ → (∀ x → (p : A.P x) → g₁ x p B.≈ᵖ g₂ x p)
      where
      module A = C⁺-ob A
      module B = C⁺-ob B

      --   --     P-subst : ∀ {Y} → {x : H.ob Y} → (f g : Y C.⇒ X)
      --   --             → f C.≈ g → P (H.hom f x) → P (H.hom g x)
      --   --     _≈ᶜ_ : ∀ {x : H.ob X} (p₁ p₂ : P x) → Prop 
      --   --     P≈-resp-hom≈
      --   --       : ∀ {Y} → {x : H.ob Y} → (f g : Y C.⇒ X)
      --   --       → (p₁ : P (H.hom f x)) (p₂ : P (H.hom g x))
      --   --       → (q : f C.≈ g)
      --   --       → P-subst f g q p₁ ≈ᶜ p₂

      --   -- -- C⁺-hom : C⁺-ob → C⁺-ob → Set
      --   -- -- C⁺-hom A B =
      --   -- --   Σ (A.X C.⇒ B.X) λ f → ∀ x → P x → Q (H.hom f x)
      --   -- --   where
      --   -- --   module A = C⁺-ob A
      --   -- --   module B = C⁺-ob B
      --   -- -- -- C⁺-hom≈ : ∀ {A B} → C⁺-hom A B → C⁺-hom A B → Prop
      --   -- -- -- C⁺-hom≈ {X , P ∶ _} {Y , Q ∶ Q-subst} (f₁ , g₁) (f₂ , g₂) =
      --   -- -- --     (f₁ C.≈ f₂)
      --   -- -- --   ∧ᵖ λ f≈ → (∀ x → (p : P x)
      --   -- -- --           → let a = Q-subst f₁ f₂ f≈ (g₁ x p)
      -- -- -- --                 b = (g₂ x p) in {!!} )
