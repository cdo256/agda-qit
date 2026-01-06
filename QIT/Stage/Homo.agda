{-# OPTIONS --type-in-type #-}
open import QIT.Prelude
open import QIT.QW

module QIT.Stage.Homo {ℓS ℓP ℓE ℓV} (qw : QW ℓS ℓP ℓE ℓV) where

open QW qw

open import QIT.Relation.Binary
open import QIT.Container
open import QIT.Setoid as ≈
open import Data.Product hiding (∃)
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Subset
open import QIT.Relation.Plump S P
open import QIT.Diagram ≤p
open import QIT.Stage.Base S P
open import Data.Maybe

private
  T = W S P

open import QIT.SystemOfEquations S P

-- We only need to expand up to the depth of some ordinal.

ιᴱ : ∀ {ℓV} {V : Set ℓV} → Expr V → Z
ιᴱ (sup (inj₁ v , f)) = ⊥ᶻ
ιᴱ (sup (inj₂ s , f)) = sup (ιˢ s , λ i → ιᴱ (f i))

_≤ᴱ_ : ∀ {ℓV} {V : Set ℓV} → Expr V → Z → Prop ℓ0
t ≤ᴱ α = ιᴱ t ≤ α

Exprᵇ : ∀ {ℓV} (V : Set ℓV) → Z → Set (ℓS ⊔ ℓP ⊔ ℓV)
Exprᵇ V α = ΣP (Expr V) (_≤ᴱ α)

private
  variable
    eq : Equation ℓV

data EqSolnᵇ : (eq : Equation ℓV) (α : Z) → Set where
  svar-l : ∀ eq α (v : V) (t : P₀ α)
         → lhs ≡ sup (inj₁ v , λ ())
         → EqSolnᵇ eq α
  -- svar-r : ∀ e  α (v : V e) (t : P₀ α)
  --        → rhs e ≡ sup (inj₁ v , λ ())
  --        → EqSolnᵇ Ξ α
  -- scong : ∀ s e Ξ (μ : P s → Z) (f g : ∀ (i : P s) → P₀ (μ i))
  --       → EqSolnᵇ {!!} {!!}

data Solnᵇ : (Ξ : SysEq ℓE ℓV) (α : Z) → Set where
  svar-l : ∀ e Ξ α (v : V e) (t : P₀ α)
         → lhs e ≡ sup (inj₁ v , λ ())
         → Solnᵇ Ξ α
  svar-r : ∀ e Ξ α (v : V e) (t : P₀ α)
         → rhs e ≡ sup (inj₁ v , λ ())
         → Solnᵇ Ξ α
  scong : ∀ s e Ξ (μ : P s → Z) (f g : ∀ (i : P s) → P₀ (μ i))
        → Solnᵇ {!!} {!!}



-- Evalᵇ : ∀ {ℓV} (V : Set ℓV) (α : Z) → (V → Maybe (P₀ α)) → Exprᵇ V α → Maybe (P₀ α)
-- Evalᵇ V₁ α x x₁ = {!!}

data Evalᵇ {ℓV} (V : Set ℓV) : (α : Z) → (V → Maybe (P₀ α)) → Exprᵇ V α → P₀ α → Set where
  evar : ∀ s μ ϕ e f
       → (p : ∀ i → Evalᵇ V (μ i) (λ v → {!!}) {!!} {!!})
       -- → (p : ∀ i → f i ≤ᵀ μ i)
       → Evalᵇ V (sup (ιˢ s , μ)) ϕ e (sup (s , f) , sup≤ λ i → <sup i {!p i!})
  

-- _⊢_[_]ᵇ : ∀ {ℓV} {V : Set ℓV} → (α : Z) → (V → T) → Exprᵇ V α → T
-- α ⊢ ϕ [ (sup (inj₁ v , _) , ≤α) ]ᵇ = ϕ v
-- sup (σ , μ) ⊢ ϕ [ (sup (inj₂ s , f) , ≤μ̃) ]ᵇ = sup (s , λ i → μ i ⊢ ϕ [ f i , {!!} ]ᵇ)

data _⊢_≈ᵇ_ : (α : Z) → P₀ α → P₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV) where
  ≈pcong : ∀ a μ (f g : ∀ i → P₀ (μ i))
         → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
         → sup (ιˢ a , μ) ⊢ psup a μ f ≈ᵇ psup a μ g
  ≈peq : ∀ α e (ϕ : V e → T) → {!!} ⊢ {!!} ≈ᵇ {!!}
  -- s t → (u : ⟦ Ξ ⟧[ s .fst ≈ t .fst ]) → α ⊢ s ≈ᵇ t
  ≈psym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ ŝ
  ≈ptrans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ û → α ⊢ ŝ ≈ᵇ û
  ≈pweaken : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : P₀ α}
          → α ⊢ ŝ ≈ᵇ t̂ → β ⊢ pweaken α≤β ŝ ≈ᵇ pweaken α≤β t̂

-- P : (α : Z) → Setoid ℓ0 ℓ0
-- P α = record
--   { Carrier = P₀ α
--   ; _≈_ = α ⊢_≈ᵇ_
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
--     e : α ⊢ (s , s≤α) ≈ᵇ (t , t≤α)

-- _≈ᵇᴵ_ : (s t : T) → Prop
-- s ≈ᵇᴵ t = ∥ ≈PI s t ∥ 

-- pattern mkPI α s≤α t≤α e = ∣ mkPI' α s≤α t≤α e ∣

-- ≈pirefl : ∀ {s} → s ≈ᵇᴵ s
-- ≈pirefl {s} = mkPI (ιᶻ s) (≤refl (ιᶻ s)) (≤refl (ιᶻ s)) ≈prefl

-- ≈pisym : ∀ {s t} → s ≈ᵇᴵ t → t ≈ᵇᴵ s
-- ≈pisym ∣ p ∣ = mkPI p.α p.t≤α p.s≤α (≈psym p.e)
--   where
--   module p = ≈PI p

-- ≈pitrans : ∀ {s t u} → s ≈ᵇᴵ t → t ≈ᵇᴵ u → s ≈ᵇᴵ u
-- ≈pitrans ∣ p ∣ ∣ q ∣ = mkPI (p.α ∨ᶻ q.α) (≤≤ ∨ᶻ-l p.s≤α) (≤≤ ∨ᶻ-r q.t≤α)
--   (≈ptrans (≈pweaken ∨ᶻ-l p.e) (≈pweaken ∨ᶻ-r q.e))
--   where
--   module p = ≈PI p
--   module q = ≈PI q

-- Pᴵ : Setoid ℓ0 ℓ0
-- Pᴵ = record
--   { Carrier = T
--   ; _≈_ = _≈ᵇᴵ_
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
