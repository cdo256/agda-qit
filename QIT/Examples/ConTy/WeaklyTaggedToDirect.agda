open import QIT.Prelude

module QIT.Examples.ConTy.WeaklyTaggedToDirect
  ⦃ pathElim* : PathElim ⦄
  where

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

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

F₀ : W.Algebra ℓA → D.Algebra ℓA
F₀ {ℓA} wa = da
  module F₀ where
  open ≡
  module WA = W.Algebra wa
  open WA using (CT; [_]; ĉ; t̂)
  Con : Set ℓA
  Con = ΣP CT λ γ → [ γ ] ≡ ĉ
  Ty : Con → Set ℓA
  Ty (γ , _) = ΣP CT λ a → [ a ] ≡ t̂ γ
  Ty-fst : ∀ {γ δ : Con} {a : Ty γ} → (r : γ ≡ δ) → subst Ty r a .fst ≡ a .fst
  Ty-fst refl = refl
  ∙ : Con
  ∙ = WA.∙ , WA.k∙
  _▷_ : (γ : Con) → Ty γ → Con
  (γ , kγ) ▷ (a , ka) = WA.▷ γ a , WA.k▷ γ a kγ ka
  u : (γ : Con) → Ty γ
  u (γ , kγ) = WA.u γ , WA.ku γ kγ
  -- Goal: {γ : Con} (a : Ty γ) → Ty (γ ▷ a) → Ty γ
  π : (γ : Con) (a : Ty γ) → Ty (γ ▷ a) → Ty γ
  π (γ , kγ) (a , ka) (b , kb) = WA.π γ a b , WA.kπ γ a b kγ ka kb
  σ : (γ : Con) (a : Ty γ) → Ty (γ ▷ a) → Ty γ
  σ (γ , kγ) (a , ka) (b , kb) = WA.σ γ a b , WA.kσ γ a b kγ ka kb
  σ▷ : (γ : Con) (a : Ty γ) (b : Ty (γ ▷ a))
     → ((γ ▷ a) ▷ b) ≡ (γ ▷ σ γ a b)
  σ▷ (γ , kγ) (a , ka) (b , kb) =
    ΣP≡ _ _ (WA.σ▷ γ a b kγ ka kb)
  σπ : (γ : Con) (a : Ty γ) (b : Ty (γ ▷ a)) (c : Ty ((γ ▷ a) ▷ b))
     → π γ a (π (γ ▷ a) b c) ≡ π γ (σ γ a b) (subst Ty (σ▷ γ a b) c)
  σπ (γ , kγ) (a , ka) (b , kb) (c , kc) =
    ΣP≡ _ _ p
    where
    open ≡.≡-Reasoning
    p : WA.π γ a (WA.π (WA.▷ γ a) b c)
      ≡ WA.π γ (WA.σ γ a b) (subst Ty (σ▷ (γ , kγ) (a , ka) (b , kb)) (c , kc) .fst)
    p =
      WA.π γ a (WA.π (WA.▷ γ a) b c)
        ≡⟨ WA.σπ γ a b c kγ ka kb kc ⟩
      WA.π γ (WA.σ γ a b) c
        ≡⟨ cong (WA.π γ (WA.σ γ a b)) (≡.sym (Ty-fst (σ▷ (γ , kγ) (a , ka) (b , kb)))) ⟩
      WA.π γ (WA.σ γ a b) (subst Ty (σ▷ (γ , kγ) (a , ka) (b , kb)) (c , _) .fst) ∎

  da : D.Algebra ℓA
  da = record
    { Con = Con
    ; Ty = Ty
    ; ∙ = ∙
    ; _▷_ = _▷_ 
    ; u = u
    ; π = π
    ; σ = σ
    ; σ▷ = σ▷
    ; σπ = σπ
    }

F₁ : ∀ {A : W.Algebra ℓA} {B : W.Algebra ℓB}
   → W.Hom A B → D.Hom (F₀ A) (F₀ B)
F₁ {ℓA} {A} {B} f = record
  { conᴿ = conᴿ
  ; tyᴿ = tyᴿ
  ; ∙ᴿ = ∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module F₁ where
  module A = W.Algebra A
  module B = W.Algebra B 
  module f = W.Hom f
  open ≡.≡-Reasoning
  conᴿ : F₀.Con A → F₀.Con B
  conᴿ (γ , kγ) = f.θ γ , ≡.trans (≡.sym f.[ γ ]) (≡.trans (≡.cong f.θ kγ) f.ĉ)
  tyᴿ : (γ : F₀.Con A) → F₀.Ty A γ → F₀.Ty B (conᴿ γ)
  tyᴿ (γ , kγ) (a , ka) = f.θ a , ka'
    where
    ka' : B.[ f.θ a ] ≡ B.t̂ (conᴿ (γ , kγ) .fst)
    ka' =
      B.[ f.θ a ]
        ≡⟨ ≡.sym f.[ a ] ⟩
      f.θ A.[ a ]
        ≡⟨ ≡.cong f.θ ka ⟩
      f.θ (A.t̂ γ)
        ≡⟨ f.t̂ γ ⟩
      B.t̂ (f.θ γ) ∎

  ∙ᴿ : conᴿ (F₀.∙ A) ≡ F₀.∙ B
  ∙ᴿ = ΣP≡ _ _ f.∙

  ▷ᴿ : (γ : F₀.Con A) (a : F₀.Ty A γ) → conᴿ (F₀._▷_ A γ a) ≡ F₀._▷_ B (conᴿ γ) (tyᴿ γ a)
  ▷ᴿ (γ , kγ) (a , ka) = ΣP≡ _ _ (f.▷ γ a kγ ka)

  uᴿ : (γ : F₀.Con A) → tyᴿ γ (F₀.u A γ) ≡ F₀.u B (conᴿ γ)
  uᴿ (γ , kγ) = ΣP≡ _ _ (f.u γ kγ)

  πᴿ : (γ : F₀.Con A) (a : F₀.Ty A γ) (b : F₀.Ty A (F₀._▷_ A γ a))
    → tyᴿ γ (F₀.π A γ a b)
    ≡ F₀.π B (conᴿ γ) (tyᴿ γ a) (subst (F₀.Ty B) (▷ᴿ γ a) (tyᴿ (F₀._▷_ A γ a) b))
  πᴿ (γ , kγ) (a , ka) (b , kb) = ΣP≡ _ _ p
    where
    p : f.θ (A.π γ a b)
      ≡ B.π (f.θ γ) (f.θ a) (subst (F₀.Ty B) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (A.▷ γ a , A.k▷ γ a kγ ka) (b , kb)) .fst)
    p =
      f.θ (A.π γ a b)
        ≡⟨ f.π γ a b kγ ka kb ⟩
      B.π (f.θ γ) (f.θ a) (f.θ b)
        ≡⟨ ≡.cong (B.π (f.θ γ) (f.θ a)) (≡.sym (F₀.Ty-fst B (▷ᴿ (γ , kγ) (a , ka)))) ⟩
      B.π (f.θ γ) (f.θ a) (subst (F₀.Ty B) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (A.▷ γ a , A.k▷ γ a kγ ka) (b , kb)) .fst) ∎

  σᴿ : (γ : F₀.Con A) (a : F₀.Ty A γ) (b : F₀.Ty A (F₀._▷_ A γ a))
    → tyᴿ γ (F₀.σ A γ a b)
    ≡ F₀.σ B (conᴿ γ) (tyᴿ γ a) (subst (F₀.Ty B) (▷ᴿ γ a) (tyᴿ (F₀._▷_ A γ a) b))
  σᴿ (γ , kγ) (a , ka) (b , kb) = ΣP≡ _ _ p
    where
    p : f.θ (A.σ γ a b)
      ≡ B.σ (f.θ γ) (f.θ a) (subst (F₀.Ty B) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (A.▷ γ a , A.k▷ γ a kγ ka) (b , kb)) .fst)
    p =
      f.θ (A.σ γ a b)
        ≡⟨ f.σ γ a b kγ ka kb ⟩
      B.σ (f.θ γ) (f.θ a) (f.θ b)
        ≡⟨ ≡.cong (B.σ (f.θ γ) (f.θ a)) (≡.sym (F₀.Ty-fst B (▷ᴿ (γ , kγ) (a , ka)))) ⟩
      B.σ (f.θ γ) (f.θ a) (subst (F₀.Ty B) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (A.▷ γ a , A.k▷ γ a kγ ka) (b , kb)) .fst) ∎

F : ∀ ℓA → Functor (W.Cat ℓA) (D.Cat ℓA) 
F ℓA = record
  { ob = F₀
  ; hom = F₁
  ; id = λ {A} → id {A}
  ; comp = comp
  ; resp = resp }
  where
  module WCat = Category (W.Cat ℓ0)
  id : ∀ {A : W.Algebra ℓA} → F₁ (W.id {ℓA} {A}) D.≈ D.id
  id {A} = D.mk≈ (λ _ → ≡.refl) λ _ _ → ≡.refl
  comp : ∀ {A₁ A₂ A₃ : W.Algebra ℓA}
       → (f : W.Hom A₁ A₂) (g : W.Hom A₂ A₃)  → F₁ (g W.∘ f) D.≈ (F₁ g D.∘ F₁ f)
  comp {A₁} {A₂} {A₃} f g = D.mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  resp : ∀ {A B : W.Algebra ℓA} {f g : W.Hom A B}
       → f W.≈ g → F₁ f D.≈ F₁ g
  resp {A} {B} {f} {g} p = D.mk≈ q r
    where
    open ≡.≡-Reasoning
    module A = W.Algebra A
    module B = W.Algebra B
    module f = W.Hom f
    module g = W.Hom g
    module p = W._≈_ p
    q : (γ : F₀.Con A) → F₁.conᴿ f γ ≡ F₁.conᴿ g γ
    q (γ , kγ) = ΣP≡ _ _ (p.θ≡ γ)
    r : (γ : F₀.Con A) (a : F₀.Ty A γ) →
         subst (F₀.Ty B) (q γ) (F₁.tyᴿ f γ a) ≡ F₁.tyᴿ g γ a
    r (γ , kγ) (a , ka) =
      ΣP≡ _ _ (≡.trans (F₀.Ty-fst B (q (γ , kγ))) (p.θ≡ a))
