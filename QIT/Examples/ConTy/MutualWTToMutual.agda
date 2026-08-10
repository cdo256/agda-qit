open import QIT.Prelude

module QIT.Examples.ConTy.MutualWTToMutual
  ⦃ pathElim* : PathElim ⦄
  where

import QIT.Examples.ConTy.MutualProjection as M
import QIT.Examples.ConTy.MutualWeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.Types
open import QIT.Maybe
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Category.Base

F₀ : W.Algebra ℓA → M.Algebra ℓA
F₀ {ℓA} wa = da
  module F₀ where
  open ≡
  module WA = W.Algebra wa
  open WA using (CT; [_]; ĉ; t̂)
  Con : Set ℓA
  Con = ΣP CT λ γ → [ γ ] ≡ ĉ
  Ty : Set ℓA
  Ty = ΣP CT λ a → [ a ] ≡ t̂
  ty₁ : Ty → Con
  ty₁ (a , ka) = WA.ty₁ a , WA.kty₁ a ka
  ∙ : Con
  ∙ = WA.∙ , WA.k∙
  ▷ : ∀ (γ : Con) (a : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → Con
  ▷ (γ , kγ) (a , ka) a₁ = WA.▷ γ a , WA.k▷ γ a kγ ka (cong fst a₁)
  u : (γ : Con) → Ty
  u (γ , kγ) = WA.u γ , WA.ku γ kγ
  u₁ : (γ : Con) → ty₁ (u γ) ≡ γ
  u₁ (γ , kγ) = ΣP≡ _ _ (WA.u₁ γ kγ)
  π : (γ : Con) (a b : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ ▷ γ a a₁)
    → Ty
  π (γ , kγ) (a , ka) (b , kb) a₁ b₁ =
    WA.π γ a b , WA.kπ γ a b kγ ka (cong fst a₁) kb (cong fst b₁)
  π₁ : (γ : Con) (a b : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ ▷ γ a a₁)
    → ty₁ (π γ a b a₁ b₁) ≡ γ
  π₁ (γ , kγ) (a , ka) (b , kb) a₁ b₁ =
    ΣP≡ (WA.ty₁ (WA.π γ a b) , _) (γ , kγ)
      (WA.π₁ γ a b (WA.kπ γ a b kγ ka (cong fst a₁) kb (cong fst b₁)))
  σ : (γ : Con) (a b : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ ▷ γ a a₁)
    → Ty
  σ (γ , kγ) (a , ka) (b , kb) a₁ b₁ =
    WA.σ γ a b , WA.kσ γ a b kγ ka (cong fst a₁) kb (cong fst b₁)
  σ₁ : (γ : Con) (a b : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ ▷ γ a a₁)
    → ty₁ (σ γ a b a₁ b₁) ≡ γ
  σ₁ (γ , kγ) (a , ka) (b , kb) a₁ b₁ =
    ΣP≡ (WA.ty₁ (WA.σ γ a b) , _) (γ , kγ)
      (WA.σ₁ γ a b (WA.kσ γ a b kγ ka (cong fst a₁) kb (cong fst b₁)))
  σ▷ : (γ : Con) (a b : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ ▷ γ a a₁)
    → ▷ (▷ γ a a₁) b b₁
    ≡ ▷ γ (σ γ a b a₁ b₁) (σ₁ γ a b a₁ b₁)
  σ▷ (γ , kγ) (a , ka) (b , kb) a₁ b₁ = ΣP≡ _ _ p
    where
    p : WA.▷ (WA.▷ γ a) b ≡ WA.▷ γ (WA.σ γ a b)
    p = WA.σ▷ γ a b kγ ka (cong fst a₁) kb (cong fst b₁)
  σπ : (γ : Con) (a b c : Ty)
    → (a₁ : ty₁ a ≡ γ)
    → (b₁ : ty₁ b ≡ ▷ γ a a₁)
    → (c₁ : ty₁ c ≡ ▷ (▷ γ a a₁) b b₁)
    → π γ a (π (▷ γ a a₁) b c b₁ c₁)
          a₁ (π₁ (▷ γ a a₁) b c b₁ c₁)
    ≡ π γ (σ γ a b a₁ b₁) c
          (σ₁ γ a b a₁ b₁)
          (≡.trans c₁ (σ▷ γ a b a₁ b₁))
  σπ (γ , kγ) (a , ka) (b , kb) (c , kc) a₁ b₁ c₁ =
    ΣP≡ _ _ (WA.σπ γ a b c kγ ka (cong fst a₁) kb (cong fst b₁) kc (cong fst c₁))

  da : M.Algebra ℓA
  da = record
    { Con = Con
    ; Ty = Ty
    ; ty₁ = ty₁
    ; ∙ = ∙
    ; ▷ = ▷
    ; u = u
    ; u₁ = u₁
    ; π = π
    ; π₁ = π₁
    ; σ = σ
    ; σ₁ = σ₁
    ; σ▷ = σ▷
    ; σπ = σπ
    }

F₁ : ∀ {A : W.Algebra ℓA} {B : W.Algebra ℓB}
   → W.Hom A B → M.Hom (F₀ A) (F₀ B)
F₁ {A = A} {B} f = record
  { conᴿ = conᴿ
  ; tyᴿ = tyᴿ
  ; ty₁ᴿ = ty₁ᴿ
  ; ∙ᴿ = ∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module F₁ where
  module A = W.Algebra A
  module B = W.Algebra B 
  module f = W.Hom f

  conᴿ : F₀.Con A → F₀.Con B
  conᴿ (γ , kγ) =
    f.θ γ , ≡.trans (≡.sym (f.[_] γ)) (≡.trans (≡.cong f.θ kγ) f.ĉ)

  tyᴿ : F₀.Ty A → F₀.Ty B
  tyᴿ (a , ka) =
    f.θ a , ≡.trans (≡.sym (f.[_] a)) (≡.trans (≡.cong f.θ ka) f.t̂)

  ty₁ᴿ : ∀ a → F₀.ty₁ B (tyᴿ a) ≡ conᴿ (F₀.ty₁ A a)
  ty₁ᴿ (a , ka) = ΣP≡ _ _ (≡.sym (f.ty₁ a))

  ∙ᴿ : conᴿ (F₀.∙ A) ≡ F₀.∙ B
  ∙ᴿ = ΣP≡ _ _ f.∙

  ▷ᴿ : ∀ γ a
    → (a₁ : F₀.ty₁ A a ≡ γ)
    → (a₁' : F₀.ty₁ B (tyᴿ a) ≡ conᴿ γ)
    → conᴿ (F₀.▷ A γ a a₁) ≡ F₀.▷ B (conᴿ γ) (tyᴿ a) a₁'
  ▷ᴿ (γ , kγ) (a , ka) a₁ a₁' =
    ΣP≡ _ _ (f.▷ γ a kγ ka (≡.cong fst a₁))

  uᴿ : (γ : F₀.Con A) → tyᴿ (F₀.u A γ) ≡ F₀.u B (conᴿ γ)
  uᴿ (γ , kγ) = ΣP≡ _ _ (f.u γ kγ)

  πᴿ : ∀ γ a b
    → (a₁ : F₀.ty₁ A a ≡ γ)
    → (b₁ : F₀.ty₁ A b ≡ F₀.▷ A γ a a₁)
    → (a₁' : F₀.ty₁ B (tyᴿ a) ≡ conᴿ γ)
    → (b₁' : F₀.ty₁ B (tyᴿ b) ≡ F₀.▷ B (conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (F₀.π A γ a b a₁ b₁)
    ≡ F₀.π B (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  πᴿ (γ , kγ) (a , ka) (b , kb) a₁ b₁ a₁' b₁' =
    ΣP≡ _ _
      (f.π γ a b kγ ka (≡.cong fst a₁) kb (≡.cong fst b₁))

  σᴿ : ∀ γ a b
    → (a₁ : F₀.ty₁ A a ≡ γ)
    → (b₁ : F₀.ty₁ A b ≡ F₀.▷ A γ a a₁)
    → (a₁' : F₀.ty₁ B (tyᴿ a) ≡ conᴿ γ)
    → (b₁' : F₀.ty₁ B (tyᴿ b) ≡ F₀.▷ B (conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (F₀.σ A γ a b a₁ b₁)
    ≡ F₀.σ B (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  σᴿ (γ , kγ) (a , ka) (b , kb) a₁ b₁ a₁' b₁' =
    ΣP≡ _ _
      (f.σ γ a b kγ ka (≡.cong fst a₁) kb (≡.cong fst b₁))

F : ∀ ℓA → Functor (W.Cat ℓA) (M.Cat ℓA) 
F ℓA = record
  { ob = F₀
  ; hom = F₁
  ; id = λ {A} → id {A}
  ; comp = comp
  ; resp = resp }
  where
  id : ∀ {A : W.Algebra ℓA} → F₁ (W.id {ℓA} {A}) M.≈ M.id
  id = M.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)

  comp : ∀ {A₁ A₂ A₃ : W.Algebra ℓA}
       → (f : W.Hom A₁ A₂) (g : W.Hom A₂ A₃)  → F₁ (g W.∘ f) M.≈ (F₁ g M.∘ F₁ f)
  comp f g = M.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)

  resp : ∀ {A B : W.Algebra ℓA} {f g : W.Hom A B}
       → f W.≈ g → F₁ f M.≈ F₁ g
  resp {A} {B} {f} {g} p = M.mk≈ q r
    where
    open ≡.≡-Reasoning
    module A = W.Algebra A
    module B = W.Algebra B
    module f = W.Hom f
    module g = W.Hom g
    module p = W._≈_ p
    q : (γ : F₀.Con A) → F₁.conᴿ f γ ≡ F₁.conᴿ g γ
    q (γ , kγ) = ΣP≡ _ _ (p.θ≡ γ)
    r : (a : F₀.Ty A) → F₁.tyᴿ f a ≡ F₁.tyᴿ g a
    r (a , ka) = ΣP≡ _ _ (p.θ≡ a)
