open import QIT.Prelude

module QIT.Stage.Homo {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Relation.Binary
open import QIT.Container
open import QIT.Setoid as ≈
open import Data.Product hiding (∃)
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Plump S P
open import QIT.Relation.Subset
open import QIT.Diagram ≤p hiding (_≤_)

private
  T = W S P

P₀ : (α : Z) → Set (ℓS ⊔ ℓP)
P₀ α = ΣP T (_≤ᵀ α)

psup : ∀ s μ (f : ∀ i → P₀ (μ i)) → P₀ (sup (ιˢ s , μ))
psup s μ f = sup (s , λ i → f i .fst) , sup≤ (λ i → <sup i (f i .snd))

⊥≤t : ∀ α → ⊥ᶻ ≤ α
⊥≤t _ = sup≤ λ ()

pweaken : ∀ {α β} → α ≤ β → P₀ α → P₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

data _⊢_≈ᴾ_ : (α : Z) → P₀ α → P₀ α → Prop {!!} where
  ≈pcong : ∀ a μ (f g : ∀ i → P₀ (μ i))
         → (r : ∀ i → μ i ⊢ f i ≈ᴾ g i)
         → sup (ιˢ a , μ) ⊢ psup a μ f ≈ᴾ psup a μ g
  ≈pquot : {!!}
  ≈psym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᴾ t̂ → α ⊢ t̂ ≈ᴾ ŝ
  ≈ptrans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᴾ t̂ → α ⊢ t̂ ≈ᴾ û → α ⊢ ŝ ≈ᴾ û
  ≈pweaken : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : P₀ α}
          → α ⊢ ŝ ≈ᴾ t̂ → β ⊢ pweaken α≤β ŝ ≈ᴾ pweaken α≤β t̂

-- P : (α : Z) → Setoid ℓ0 ℓ0
-- P α = record
--   { Carrier = P₀ α
--   ; _≈_ = α ⊢_≈ᴾ_
--   ; isEquivalence = record
--     { refl = ≈prefl
--     ; sym = ≈psym
--     ; trans = ≈ptrans  } }

-- record ≈PI (s t : T) : Set where
--   constructor mkPI'
--   field
--     α : Z
--     s≤α : s ≤ᵀ α
--     t≤α : t ≤ᵀ α
--     e : α ⊢ (s , s≤α) ≈ᴾ (t , t≤α)

-- _≈ᴾᴵ_ : (s t : T) → Prop
-- s ≈ᴾᴵ t = ∥ ≈PI s t ∥ 

-- pattern mkPI α s≤α t≤α e = ∣ mkPI' α s≤α t≤α e ∣

-- ≈pirefl : ∀ {s} → s ≈ᴾᴵ s
-- ≈pirefl {s} = mkPI (ιᶻ s) (≤refl (ιᶻ s)) (≤refl (ιᶻ s)) ≈prefl

-- ≈pisym : ∀ {s t} → s ≈ᴾᴵ t → t ≈ᴾᴵ s
-- ≈pisym ∣ p ∣ = mkPI p.α p.t≤α p.s≤α (≈psym p.e)
--   where
--   module p = ≈PI p

-- ≈pitrans : ∀ {s t u} → s ≈ᴾᴵ t → t ≈ᴾᴵ u → s ≈ᴾᴵ u
-- ≈pitrans ∣ p ∣ ∣ q ∣ = mkPI (p.α ∨ᶻ q.α) (≤≤ ∨ᶻ-l p.s≤α) (≤≤ ∨ᶻ-r q.t≤α)
--   (≈ptrans (≈pweaken ∨ᶻ-l p.e) (≈pweaken ∨ᶻ-r q.e))
--   where
--   module p = ≈PI p
--   module q = ≈PI q

-- Pᴵ : Setoid ℓ0 ℓ0
-- Pᴵ = record
--   { Carrier = T
--   ; _≈_ = _≈ᴾᴵ_
--   ; isEquivalence = record
--     { refl = ≈pirefl
--     ; sym = ≈pisym
--     ; trans = ≈pitrans  } }

-- D : Diagram ℓ0 ℓ0
-- D = record
--   { D-ob = P
--   ; D-mor = Hom
--   ; D-id = Id
--   ; D-comp = Comp }
--   where
--   Hom : ∀ {α β} → α ≤ β → ≈.Hom (P α) (P β)
--   Hom {α} {β} α≤β = record
--     { to = pweaken α≤β
--     ; cong = ≈pweaken α≤β }
--   Id : ∀ {α} → (Hom (≤refl α)) ≈h ≈.idHom
--   Id {α} {ŝ} {t̂} p = p
--   Comp : ∀ {α β γ} (p : α ≤ β) (q : β ≤ γ) →
--       Hom (≤≤ q p) ≈h (Hom q ≈.∘ Hom p)
--   Comp {α} {β} {γ} p q {ŝ} {t̂} s≈t = ≈pweaken q (≈pweaken p s≈t)
