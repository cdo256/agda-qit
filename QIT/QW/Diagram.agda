open import QIT.Prelude hiding (ℓD)
open import QIT.Prop
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient
open import QIT.Plump.Algebra
open import QIT.Relation.Binary

-- Define staged construction of quotient W-types using plump ordinals.
-- This builds the quotient in stages indexed by ordinals, ensuring that
-- equations are satisfied at each stage. The construction uses diagrams
-- indexed by the plump ordinal order to control the complexity of terms.
module QIT.QW.Diagram
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  {ℓZ ℓ< ℓ≤} (Zᴬ : PlumpAlgebra (sig .Sig.S) (sig .Sig.P) ℓZ ℓ< ℓ≤)
  where
open Sig sig
open FunExt funExt*

open import QIT.Plump.Properties Zᴬ as Z

open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base using (_≡h_)
open import QIT.QW.Stage sig Zᴬ
open import QIT.Category.Preorder
open import QIT.Category.Setoid
open import QIT.Category.Set
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Setoid.Hom 

open SQ

open import QIT.Functor.Diagram ≤p

private
  ℓD = ℓ≤ ⊔ ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV

open Box

D̃ : Diagram ℓD ℓD'
D̃ = record
  { ob = S̃
  ; hom = λ (box p) → dweaken p
  ; id = ≈trefl
  ; comp = λ _ _ → ≈trefl
  ; resp = λ _ → ≈trefl }

open import QIT.Category.Base
module ≤p = Category (PreorderCat Z ≤p)
open import QIT.Category.Equivalence
open import QIT.Category.Set
module SetCat = Category (SetCat (ℓD ⊔ ℓD'))

hom₀ : ∀ {α β} → Box (α ≤ β) → S₀ α → S₀ β
hom₀ (box p) = dweaken₀ p 

hom/ : ∀ {α β} → Box (α ≤ β) → S̃/ α → S̃/ β
hom/ (box p) = dweaken/ p

hom-beta : ∀ {α β} → (p : Box (α ≤ β)) → (s : S₀ α)
          → hom/ p (S̃ α ⊢[ s ]) ≡ (S̃ β ⊢[ hom₀ p s ])
hom-beta (box p) = dweaken-beta p

id : ∀ {α} → hom/ ≤p.id ≡h SetCat.id
id {α} {t̃} = q t̃
  where
  q : ∀ t̃ → hom/ {α} ≤p.id t̃ ≡ t̃
  q = SQ.elimp (S̃ α) (λ t̃ → dweaken/ {α} (≤refl α) t̃ ≡ t̃)
                      (dweaken-beta (≤refl α))

open ≡.≡-Reasoning
comp : ∀ {α β γ} (f : Box (α ≤ β)) (g : Box (β ≤ γ))
      → hom/ (g ≤p.∘ f) ≡h (hom/ g SetCat.∘ hom/ f)
comp {α} {β} {γ} (box f) (box g) {t̃} = Qα.elimp _ r t̃
  where
  module Qα = SQ (S̃ α)
  r : (s : S₀ α)
    → hom/ (box g ≤p.∘ box f) (S̃ α ⊢[ s ])
    ≡ (hom/ (box g) SetCat.∘ hom/ (box f)) (S̃ α ⊢[ s ])
  r s = 
    hom/ (box g ≤p.∘ box f) (S̃ α ⊢[ s ])
      ≡⟨ hom-beta (box (≤≤ g f)) s ⟩
    S̃ γ ⊢[ dweaken₀ (≤≤ g f) s ]
      ≡⟨ ≡.sym (hom-beta (box g) (dweaken₀ f s)) ⟩
    hom/ (box g) (S̃ β ⊢[ dweaken₀ f s ])
      ≡⟨ ≡.cong (hom/ (box g)) (≡.sym (hom-beta (box f) s)) ⟩
    hom/ (box g) (hom/ (box f) (S̃ α ⊢[ s ])) ∎

open import QIT.Function.Base
open import QIT.Set.Bijection

isInjHom : ∀ {α β} (p : α ≤ β)
        → ∀ {x y} → hom/ (box p) (S̃ α ⊢[ x ]) ≡ hom/ (box p) (S̃ α ⊢[ y ])
        → _≡_ {A = S̃ α /≈} (S̃ α ⊢[ x ]) (S̃ α ⊢[ y ])
isInjHom {α} {β} α≤β {x} {y} q =
  Qα.≈[ Qβ.effectiveness _ _ q' ]
  where
  module Qα = SQ (S̃ α)
  module Qβ = SQ (S̃ β)

  q' : Qβ.[ dweaken₀ α≤β x ] ≡ Qβ.[ dweaken₀ α≤β y ]
  q' =
    S̃ β ⊢[ dweaken₀ α≤β x ]
      ≡⟨ ≡.sym (dweaken-beta α≤β x) ⟩
    dweaken/ α≤β (S̃ α ⊢[ x ])
      ≡⟨ q ⟩
    dweaken/ α≤β (S̃ α ⊢[ y ])
      ≡⟨ dweaken-beta α≤β y ⟩
    S̃ β ⊢[ dweaken₀ α≤β y ] ∎

-- Morphisms are weakening maps preserving equivalence
hom≈ : ∀ {α β} → Box (α ≤ β) → ≈.Hom (S̃ α) (S̃ β)
hom≈ {α} {β} (box α≤β) = record
  { to = dweaken₀ α≤β
  ; cong = λ z → z }

subst-S₀-fst : ∀ {γ δ} (p : γ ≡ δ) (û : S₀ γ) → ⟨ subst S₀ p û ⟩ᴾ ≡ ⟨ û ⟩ᴾ
subst-S₀-fst {γ} ≡.refl û = ≡.cong ⟨_⟩ᴾ (subst-refl {B = S₀} û)

-- Container functor
open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
open import QIT.Setoid.Quotient using (_/≈)

-- Colimits and cocontinuity
open import QIT.Colimit Z.≤p ℓD ℓD' hiding (_≈ˡ_)

open import QIT.Functor.Properties

D̃/ : Functor (PreorderCat Z ≤p)
             (SetCat (ℓD ⊔ ℓD'))
D̃/ = D̃ /≈ᴰ

-- Module aliases for cleaner notation
module F = Functor F
module D̃ = Functor D̃
module D̃/ = Functor (D̃ /≈ᴰ)
module F∘D = Functor (F ∘ꟳ D̃/)

-- The underlying W-type of trees before quotienting.
T = W S P
