open import QIT.Prelude
open import QIT.QW
import QIT.Relation.Plump as Plump

module QIT.Stage.Homo {ℓS ℓP ℓE ℓV} (qw : QW ℓS ℓP ℓE ℓV) (α : Plump.Z (qw .QW.S) (qw .QW.P)) where 

open QW qw

open import QIT.Relation.Binary
open import QIT.Container
open import QIT.Setoid as ≈
open import Data.Product hiding (∃)
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Subset
open Plump S P
open import QIT.Diagram ≤p
open import QIT.Stage.Base S P

private
  T = W S P

open import QIT.SystemOfEquations S P hiding (_[_])

Exprᵇ : ∀ {ℓV} (V : Set ℓV) → Set (ℓS ⊔ ℓP ⊔ ℓV)
Exprᵇ {ℓV} V = W Sʰ Pʰ
  where
  Sʰ : Set (ℓS ⊔ ℓV)
  Sʰ = V ⊎ S
  Pʰ : Sʰ → Set ℓP
  Pʰ = [ (λ _ → ⊥*) , P ]

-- Φ : ∀ α → Exprᵇ V

data _≈ᵇ_ : P₀ α → P₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV) where
  ≈pcong : ∀ a μ (f g : ∀ i → P₀ (μ i))
         → (r : ∀ i → f i ≈ᴾ g i)
         → sup (ιˢ a , μ) ⊢ psup a μ f ≈ᴾ psup a μ g
  ≈peq : ∀ α e s t → (u : {!!}) → α ⊢ s ≈ᴾ t
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
