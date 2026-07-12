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

F₀ : W.Algebra ℓX → D.Algebra ℓX
F₀ {ℓX} wa = da
  module F₀ where
  open ≡
  module WA = W.Algebra wa
  open WA using (CT; [_]; ĉ; t̂)
  Con : Set ℓX
  Con = ΣP CT λ γ → [ γ ] ≡ ĉ
  Ty : Con → Set ℓX
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

  da : D.Algebra ℓX
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

F₁ : ∀ {α β : W.Algebra ℓX}
   → W.Hom α β → D.Hom (F₀ α) (F₀ β)
F₁ {ℓX} {α} {β} f = record
  { conᴿ = conᴿ
  ; tyᴿ = tyᴿ
  ; ∙ᴿ = ∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module F₁ where
  module α = W.Algebra α
  module β = W.Algebra β 
  module f = W.Hom f
  open ≡.≡-Reasoning
  conᴿ : F₀.Con α → F₀.Con β
  conᴿ (γ , kγ) = f.θ γ , ≡.trans (≡.sym f.[ γ ]) (≡.trans (≡.cong f.θ kγ) f.ĉ)
  tyᴿ : (γ : F₀.Con α) → F₀.Ty α γ → F₀.Ty β (conᴿ γ)
  tyᴿ (γ , kγ) (a , ka) = f.θ a , ka'
    where
    ka' : β.[ f.θ a ] ≡ β.t̂ (conᴿ (γ , kγ) .fst)
    ka' =
      β.[ f.θ a ]
        ≡⟨ ≡.sym f.[ a ] ⟩
      f.θ α.[ a ]
        ≡⟨ ≡.cong f.θ ka ⟩
      f.θ (α.t̂ γ)
        ≡⟨ f.t̂ γ ⟩
      β.t̂ (f.θ γ) ∎

  ∙ᴿ : conᴿ (F₀.∙ α) ≡ F₀.∙ β
  ∙ᴿ = ΣP≡ _ _ f.∙

  ▷ᴿ : (γ : F₀.Con α) (a : F₀.Ty α γ) → conᴿ (F₀._▷_ α γ a) ≡ F₀._▷_ β (conᴿ γ) (tyᴿ γ a)
  ▷ᴿ (γ , kγ) (a , ka) = ΣP≡ _ _ (f.▷ γ a kγ ka)

  uᴿ : (γ : F₀.Con α) → tyᴿ γ (F₀.u α γ) ≡ F₀.u β (conᴿ γ)
  uᴿ (γ , kγ) = ΣP≡ _ _ (f.u γ kγ)

  πᴿ : (γ : F₀.Con α) (a : F₀.Ty α γ) (b : F₀.Ty α (F₀._▷_ α γ a))
    → tyᴿ γ (F₀.π α γ a b)
    ≡ F₀.π β (conᴿ γ) (tyᴿ γ a) (subst (F₀.Ty β) (▷ᴿ γ a) (tyᴿ (F₀._▷_ α γ a) b))
  πᴿ (γ , kγ) (a , ka) (b , kb) = ΣP≡ _ _ p
    where
    p : f.θ (α.π γ a b)
      ≡ β.π (f.θ γ) (f.θ a) (subst (F₀.Ty β) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (α.▷ γ a , α.k▷ γ a kγ ka) (b , kb)) .fst)
    p =
      f.θ (α.π γ a b)
        ≡⟨ f.π γ a b kγ ka kb ⟩
      β.π (f.θ γ) (f.θ a) (f.θ b)
        ≡⟨ ≡.cong (β.π (f.θ γ) (f.θ a)) (≡.sym (F₀.Ty-fst β (▷ᴿ (γ , kγ) (a , ka)))) ⟩
      β.π (f.θ γ) (f.θ a) (subst (F₀.Ty β) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (α.▷ γ a , α.k▷ γ a kγ ka) (b , kb)) .fst) ∎

  σᴿ : (γ : F₀.Con α) (a : F₀.Ty α γ) (b : F₀.Ty α (F₀._▷_ α γ a))
    → tyᴿ γ (F₀.σ α γ a b)
    ≡ F₀.σ β (conᴿ γ) (tyᴿ γ a) (subst (F₀.Ty β) (▷ᴿ γ a) (tyᴿ (F₀._▷_ α γ a) b))
  σᴿ (γ , kγ) (a , ka) (b , kb) = ΣP≡ _ _ p
    where
    p : f.θ (α.σ γ a b)
      ≡ β.σ (f.θ γ) (f.θ a) (subst (F₀.Ty β) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (α.▷ γ a , α.k▷ γ a kγ ka) (b , kb)) .fst)
    p =
      f.θ (α.σ γ a b)
        ≡⟨ f.σ γ a b kγ ka kb ⟩
      β.σ (f.θ γ) (f.θ a) (f.θ b)
        ≡⟨ ≡.cong (β.σ (f.θ γ) (f.θ a)) (≡.sym (F₀.Ty-fst β (▷ᴿ (γ , kγ) (a , ka)))) ⟩
      β.σ (f.θ γ) (f.θ a) (subst (F₀.Ty β) (▷ᴿ (γ , kγ) (a , ka)) (tyᴿ (α.▷ γ a , α.k▷ γ a kγ ka) (b , kb)) .fst) ∎

F : ∀ ℓX → Functor (W.Cat ℓX) (D.Cat ℓX) 
F ℓX = record
  { ob = F₀
  ; hom = F₁
  ; id = λ {α} → id {α}
  ; comp = comp
  ; resp = resp }
  where
  module WCat = Category (W.Cat ℓ0)
  id : ∀ {α : W.Algebra ℓX} → F₁ (W.id {ℓX} {α}) D.≈ D.id
  id {α} = D.mk≈ (λ _ → ≡.refl) λ _ _ → ≡.refl
  comp : ∀ {α₁ α₂ α₃ : W.Algebra ℓX}
       → (f : W.Hom α₁ α₂) (g : W.Hom α₂ α₃)  → F₁ (g W.∘ f) D.≈ (F₁ g D.∘ F₁ f)
  comp {α₁} {α₂} {α₃} f g = D.mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
  resp : ∀ {α β : W.Algebra ℓX} {f g : W.Hom α β}
       → f W.≈ g → F₁ f D.≈ F₁ g
  resp {α} {β} {f} {g} p = D.mk≈ q r
    where
    open ≡.≡-Reasoning
    module α = W.Algebra α
    module β = W.Algebra β
    module f = W.Hom f
    module g = W.Hom g
    module p = W._≈_ p
    q : (γ : F₀.Con α) → F₁.conᴿ f γ ≡ F₁.conᴿ g γ
    q (γ , kγ) = ΣP≡ _ _ (p.θ≡ γ)
    r : (γ : F₀.Con α) (a : F₀.Ty α γ) →
         subst (F₀.Ty β) (q γ) (F₁.tyᴿ f γ a) ≡ F₁.tyᴿ g γ a
    r (γ , kγ) (a , ka) =
      ΣP≡ _ _ (≡.trans (F₀.Ty-fst β (q (γ , kγ))) (p.θ≡ a))
