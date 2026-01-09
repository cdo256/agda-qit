open import QIT.Prelude
open import QIT.QW.Signature

module QIT.QW.Stage {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Container.Base
open import QIT.Container.Functor S P
open import QIT.Setoid as ≈
open import QIT.Relation.Subset
open import QIT.Relation.Plump S P
open import QIT.QW.Diagram ≤p
open import QIT.QW.W sig
open import Data.Maybe
open import QIT.QW.Equation S P

D₀ : (α : Z) → Set (ℓS ⊔ ℓP)
D₀ α = ΣP T (_≤ᵀ α)

psup : ∀ a μ (f : ∀ i → D₀ (μ i)) → D₀ (sup (ιˢ a , μ))
psup a μ f = sup (a , λ i → f i .fst) , sup≤ (λ i → <sup i (f i .snd))

pweaken : ∀ {α β} → α ≤ β → D₀ α → D₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

-- We only need to expand up to the depth of some ordinal.

ιᴱ : ∀ {ℓV} {V : Set ℓV} → Expr V → Z
ιᴱ (sup (inj₁ v , f)) = ⊥ᶻ
ιᴱ (sup (inj₂ s , f)) = sup (ιˢ s , λ i → ιᴱ (f i))

_≤ᴱ_ : ∀ {ℓV} {V : Set ℓV} → Expr V → Z → Prop (ℓS ⊔ ℓP)
t ≤ᴱ α = ιᴱ t ≤ α

lhs' : ∀ e (ϕ : V {ℓV = ℓV} e → T) → T
lhs' e ϕ = assign T-alg ϕ (lhs e)

rhs' : ∀ e (ϕ : V {ℓV = ℓV} e → T) → T
rhs' e ϕ = assign T-alg ϕ (rhs e)

data _⊢_≈ᵇ_ : (α : Z) → D₀ α → D₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  ≈pcong : ∀ a μ (f g : ∀ i → D₀ (μ i))
        → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
        → sup (ιˢ a , μ) ⊢ psup a μ f ≈ᵇ psup a μ g
  ≈psat : ∀ {α} e (ϕ : V e → T)
        → (l≤α : lhs' e ϕ ≤ᵀ α)
        → (r≤α : rhs' e ϕ ≤ᵀ α)
        → α ⊢  (lhs' e ϕ , l≤α)
            ≈ᵇ (rhs' e ϕ , r≤α)
  ≈prefl : ∀ {α t̂} → α ⊢ t̂ ≈ᵇ t̂
  ≈psym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ ŝ
  ≈ptrans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ û → α ⊢ ŝ ≈ᵇ û
  ≈pweaken : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : D₀ α}
          → α ⊢ ŝ ≈ᵇ t̂ → β ⊢ pweaken α≤β ŝ ≈ᵇ pweaken α≤β t̂

D̃ : (α : Z) → Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D̃ α = record
  { Carrier = D₀ α
  ; _≈_ = α ⊢_≈ᵇ_
  ; isEquivalence = record
    { refl = ≈prefl
    ; sym = ≈psym
    ; trans = ≈ptrans } }

D : Diagram (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D = record
  { D-ob = D̃ 
  ; D-mor = Hom
  ; D-id = Id
  ; D-comp = Comp }
  where
  Hom : ∀ {α β} → α ≤ β → ≈.Hom (D̃ α) (D̃ β)
  Hom {α} {β} α≤β = record
    { to = pweaken α≤β
    ; cong = ≈pweaken α≤β }
  Id : ∀ {α} → (Hom (≤refl α)) ≈h ≈.idHom
  Id {α} {ŝ} {t̂} p = p
  Comp : ∀ {α β γ} (p : α ≤ β) (q : β ≤ γ) →
      Hom (≤≤ q p) ≈h (Hom q ≈.∘ Hom p)
  Comp {α} {β} {γ} p q {ŝ} {t̂} s≈t = ≈pweaken q (≈pweaken p s≈t)
