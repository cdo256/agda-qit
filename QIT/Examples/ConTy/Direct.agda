{-# OPTIONS --allow-unsolved-metas #-}
module QIT.Examples.ConTy.Direct where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

record Algebra : Set₁ where
  infixl 5 _▷_
  field
    Con : Set
    Ty : Con → Set
    ∙ : Con
    _▷_ : ∀ γ → Ty γ → Con
    u : (γ : Con) → Ty γ
    π : ∀ {γ} → (a : Ty γ) → (b : Ty (γ ▷ a)) → Ty γ
    σ : ∀ {γ} → (a : Ty γ) → (b : Ty (γ ▷ a)) → Ty γ
    σ▷ : ∀ {γ a b} → γ ▷ a ▷ b ≡ γ ▷ σ a b
    σπ : ∀ {γ a b c} → π {γ} a (π b c) ≡ π (σ a b) (subst Ty σ▷ c)

record Hom (A B : Algebra) : Set₁ where
  module A = Algebra A
  module B = Algebra B
  field
    conᴿ : A.Con → B.Con
    tyᴿ : ∀ γ → A.Ty γ → B.Ty (conᴿ γ)
    ∙ᴿ : conᴿ A.∙ ≡ B.∙
    ▷ᴿ : ∀ {γ} a → conᴿ (γ A.▷ a) ≡ conᴿ γ B.▷ tyᴿ γ a
    uᴿ : ∀ {γ} → tyᴿ γ (A.u γ) ≡ B.u (conᴿ γ)
    πᴿ : ∀ {γ} a b → tyᴿ γ (A.π a b) ≡ B.π (tyᴿ γ a) (subst B.Ty (▷ᴿ a) (tyᴿ (γ A.▷ a) b))
    σᴿ : ∀ {γ} a b → tyᴿ γ (A.π a b) ≡ B.π (tyᴿ γ a) (subst B.Ty (▷ᴿ a) (tyᴿ (γ A.▷ a) b))
    
record _≈_ {A B : Algebra} (f g : Hom A B) : Set₁ where
  module A = Algebra A
  module B = Algebra B
  module f = Hom f
  module g = Hom g
  field
    con≡ : ∀ γ → f.conᴿ γ ≡ g.conᴿ γ
    ty≡ : ∀ γ a → subst B.Ty (con≡ γ) (f.tyᴿ γ a) ≡ g.tyᴿ γ a
    
