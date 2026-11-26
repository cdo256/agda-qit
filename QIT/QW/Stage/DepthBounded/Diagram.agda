open import QIT.Prelude hiding (ℓD)
open import QIT.Prop
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient
open import QIT.Plump.Algebra
open import QIT.Relation.Binary

-- The diagram of depth-bounded stages.
-- This builds the quotient in stages indexed by ordinals, ensuring that
-- equations are satisfied at each stage. The construction uses diagrams
-- indexed by the plump ordinal order to control the complexity of terms.
module QIT.QW.Stage.DepthBounded.Diagram
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (Zᴬ : PlumpAlgebra (sig .Sig.S) (sig .Sig.P))
  where
  
open Sig sig
open FunExt funExt*

open PlumpAlgebra Zᴬ
open import QIT.Plump.Properties Zᴬ as Z

open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base using (_≡h_)
open import QIT.QW.Stage.DepthBounded sig Zᴬ
open import QIT.Functor.Base
open import QIT.Setoid.Hom 

open SQ

≤wp : WeakPreorder Z _
≤wp = _≤_ , record { trans = λ p q → ≤≤ q p }

open import QIT.SimpleDiagram ≤wp

private
  ℓD = ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV

D̃ : Diagram≈ ℓD ℓD'
D̃ = record
  { ob = S̃
  ; edge = dweaken
  ; nat = λ _ _ → ≈trefl }

hom₀ : ∀ {α β} → α ≤ β → S₀ α → S₀ β
hom₀ = dweaken₀

hom/ : ∀ {α β} → α ≤ β → S̃/ α → S̃/ β
hom/ = dweaken/

hom-beta : ∀ {α β} → (p : α ≤ β) → (s : S₀ α)
          → hom/ p (S̃ α ⊢[ s ]) ≡ (S̃ β ⊢[ hom₀ p s ])
hom-beta = dweaken-beta

open ≡.≡-Reasoning
comp : ∀ {α β γ} (f : α ≤ β) (g : β ≤ γ)
      → ∀ {t̃} → hom/ (≤≤ g f) t̃ ≡ hom/ g (hom/ f t̃)
comp {α} {β} {γ} f g {t̃} = Qα.elimp _ r t̃
  where
  module Qα = SQ (S̃ α)
  r : (s : S₀ α)
    → hom/ (≤≤ g f) (S̃ α ⊢[ s ])
    ≡ hom/ g (hom/ f (S̃ α ⊢[ s ]))
  r s = 
    hom/ (≤≤ g f) (S̃ α ⊢[ s ])
      ≡⟨ hom-beta (≤≤ g f) s ⟩
    S̃ γ ⊢[ dweaken₀ (≤≤ g f) s ]
      ≡⟨ ≡.sym (hom-beta g (dweaken₀ f s)) ⟩
    hom/ g (S̃ β ⊢[ dweaken₀ f s ])
      ≡⟨ ≡.cong (hom/ g) (≡.sym (hom-beta f s)) ⟩
    hom/ g (hom/ f (S̃ α ⊢[ s ])) ∎

open import QIT.Function.Base
open import QIT.Set.Bijection

isInjHom : ∀ {α β} (p : α ≤ β)
        → ∀ {x y} → hom/ p (S̃ α ⊢[ x ]) ≡ hom/ p (S̃ α ⊢[ y ])
        → _≡_ {A = S̃ α /≈} (S̃ α ⊢[ x ]) (S̃ α ⊢[ y ])
isInjHom {α} {β} α≤β {x} {y} q =
  S̃ α ⊢≈[ SQ.effectiveness (S̃ β) _ _ q' ]
  where
  q' : S̃ β ⊢[ dweaken₀ α≤β x ] ≡ S̃ β ⊢[ dweaken₀ α≤β y ]
  q' =
    S̃ β ⊢[ dweaken₀ α≤β x ]
      ≡⟨ ≡.sym (dweaken-beta α≤β x) ⟩
    hom/ α≤β (S̃ α ⊢[ x ])
      ≡⟨ q ⟩
    hom/ α≤β (S̃ α ⊢[ y ])
      ≡⟨ dweaken-beta α≤β y ⟩
    S̃ β ⊢[ dweaken₀ α≤β y ] ∎

-- Morphisms are weakening maps preserving equivalence
hom≈ : ∀ {α β} → α ≤ β → ≈.Hom (S̃ α) (S̃ β)
hom≈ {α} {β} α≤β = record
  { to = dweaken₀ α≤β
  ; cong = λ z → z }

-- Container functor
open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
module CF = Functor F
open import QIT.Setoid.Quotient using (_/≈)

-- Colimits and cocontinuity
open import QIT.Colimit ≤wp (ℓD ⊔ ℓD') hiding (_≈ˡ_)

D̃/ : Diagram (ℓD ⊔ ℓD')
D̃/ = D̃ /≈ᴰ

FD̃/ : Diagram (ℓS ⊔ ℓP ⊔ ℓD ⊔ ℓD')
FD̃/ = record
  { ob = λ α → CF.ob (Diagram.ob D̃/ α)
  ; edge = λ p → CF.hom (Diagram.edge D̃/ p)
  ; nat = λ p q (s , f) → ≡.Σ≡ ≡.refl (funExt λ i → D̃/ .Diagram.nat p q (f i)) }

-- Module aliases for cleaner notation
D* : Setoid (ℓD ⊔ ℓD') (ℓD ⊔ ℓD')
D* = Colim D̃/
D*₀ : Set (ℓD ⊔ ℓD')
D*₀ = Colim₀ D̃/
D*/ : Set (ℓD ⊔ ℓD')
D*/ = Colim/ D̃/

FD* : Setoid (ℓD ⊔ ℓD') (ℓD ⊔ ℓD')
FD* = Colim FD̃/
FD*₀ : Set (ℓD ⊔ ℓD')
FD*₀ = Colim₀ FD̃/
FD*/ : Set (ℓD ⊔ ℓD')
FD*/ = Colim/ FD̃/

-- The underlying W-type of trees before quotienting.
T = W S P
