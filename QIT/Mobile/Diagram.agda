open import QIT.Prelude

module QIT.Mobile.Diagram (I : Set) (inhabI : ∥ I ∥) where

open import QIT.Relation.Binary
open import QIT.Container.Base
open import QIT.Mobile.Base I
open import QIT.Mobile.Functor I
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Plump Sᵀ Pᵀ
open import QIT.Relation.Subset
open import QIT.QW.Diagram ≤p hiding (_≤_)

P₀ : (α : Z) → Set
P₀ α = ΣP T (_≤ᵀ α)

n≰l : ∀ {f g} → ¬p (sup (ιˢ n , f) ≤ sup (ιˢ l , g))
n≰l {f} {g} (sup≤ f<l) = r inhabI
  where
  r : ∥ I ∥ → ⊥p
  r ∣ b ∣ with f<l b
  ... | <sup () i≤fx

pnode : ∀ μ (f : ∀ i → P₀ (μ i)) → P₀ (sup (ιˢ n , μ))
pnode μ f = sup (n , λ i → f i .fst) , sup≤ (λ i → <sup i (f i .snd))

_∘ᴾ_ : ∀ {μ : I → Z} (f : (i : I) → P₀ (μ i)) (π : I ↔ I)
     → (i : I) → P₀ (μ (π .↔.to i))
_∘ᴾ_ {μ} f π = λ i → f (π .↔.to i)

pperm : ∀ (μ : I → Z) (f : (i : I) → P₀ (μ i)) (π : I ↔ I)
     → P₀ (sup (ιˢ n , μ))
pperm μ f π = t , sup≤ (λ i → <sup (π' i) (f (π' i) .snd))
  where
  π' : I → I
  π' = π .↔.to
  g : (i : I) → W Sᵀ Pᵀ
  g = λ i → f (π' i) .fst
  t : T
  t = sup (n , g)

pweaken : ∀ {α β} → α ≤ β → P₀ α → P₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

data _⊢_≈ᴾ_ : (α : Z) → P₀ α → P₀ α → Prop where
  ≈pnode : ∀ μ (f g : ∀ i → P₀ (μ i))
         → (r : ∀ i → μ i ⊢ f i ≈ᴾ g i)
         → sup (ιˢ n , μ) ⊢ pnode μ f ≈ᴾ pnode μ g
  ≈pperm : ∀ μ (f : ∀ i → P₀ (μ i)) → (π : I ↔ I)
         → sup (ιˢ n , μ) ⊢ pnode μ f ≈ᴾ pperm μ f π
  ≈prefl : ∀ {α t̂} → α ⊢ t̂ ≈ᴾ t̂
  ≈psym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᴾ t̂ → α ⊢ t̂ ≈ᴾ ŝ
  ≈ptrans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᴾ t̂ → α ⊢ t̂ ≈ᴾ û → α ⊢ ŝ ≈ᴾ û
  ≈pweaken : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : P₀ α}
          → α ⊢ ŝ ≈ᴾ t̂ → β ⊢ pweaken α≤β ŝ ≈ᴾ pweaken α≤β t̂

P : (α : Z) → Setoid ℓ0 ℓ0
P α = record
  { Carrier = P₀ α
  ; _≈_ = α ⊢_≈ᴾ_
  ; isEquivalence = record
    { refl = ≈prefl
    ; sym = ≈psym
    ; trans = ≈ptrans  } }

D : Diagram ℓ0 ℓ0
D = record
  { D-ob = P
  ; D-mor = Hom
  ; D-id = Id
  ; D-comp = Comp }
  where
  Hom : ∀ {α β} → α ≤ β → ≈.Hom (P α) (P β)
  Hom {α} {β} α≤β = record
    { to = pweaken α≤β
    ; cong = ≈pweaken α≤β }
  Id : ∀ {α} → (Hom (≤refl α)) ≈h ≈.idHom
  Id {α} {ŝ} {t̂} p = p
  Comp : ∀ {α β γ} (p : α ≤ β) (q : β ≤ γ) →
      Hom (≤≤ q p) ≈h (Hom q ≈.∘ Hom p)
  Comp {α} {β} {γ} p q {ŝ} {t̂} s≈t = ≈pweaken q (≈pweaken p s≈t)
