open import QIT.Prelude
open import QIT.QW.Signature

-- Define staged construction of quotient W-types using plump ordinals.
-- This builds the quotient in stages indexed by ordinals, ensuring that
-- equations are satisfied at each stage. The construction uses diagrams
-- indexed by the plump ordinal order to control the complexity of terms.
module QIT.QW.Stage {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Container.Base
open import QIT.Container.Functor S P
open import QIT.Setoid as ≈
open import QIT.Relation.Subset
open import QIT.Relation.Plump S P
open import QIT.Setoid.Diagram ≤p
open import QIT.QW.W S P 
open import Data.Maybe
open import QIT.QW.Equation S P ℓV

-- Stage α: elements of the underlying W-type bounded by ordinal α.
-- This gives us size-bounded approximations to the final quotient.
D₀ : (α : Z) → Set (ℓS ⊔ ℓP)
D₀ α = ΣP T (_≤ᵀ α)

-- Constructor for stage elements: build a tree with given shape and children.
-- The ordinal bound is computed from the children's bounds using plump structure.
psup : ∀ a μ (f : ∀ i → D₀ (μ i)) → D₀ (sup (ιˢ a , μ))
psup a μ f = sup (a , λ i → ⟨ f i ⟩ᴾ) , sup≤ (λ i → <sup i (f i .snd))

-- Weakening: if α ≤ β then stage α embeds into stage β.
-- This gives the morphisms in our diagram of stages.
pweaken : ∀ {α β} → α ≤ β → D₀ α → D₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

-- Ordinal complexity of expressions: measures the "depth" needed to satisfy equations.
-- Variables have minimal complexity ⊥ᶻ, constructors have complexity based on arguments.
ιᵉ : {V : Set ℓV} → Expr V → Z
ιᵉ (varᴱ v) = ⊥ᶻ
ιᵉ (supᴱ s f) = sup (ιˢ s , λ i → ιᵉ (f i))

-- Expression-ordinal comparison: when an expression fits within a stage.
_≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop (ℓS ⊔ ℓP)
t ≤ᴱ α = ιᵉ t ≤ α

-- Interpretation of equation sides as W-type elements.
-- These functions evaluate expressions in the underlying W-type T.
-- We work in T, requiring proof that the left and right substituted expressions
-- are under the bound α. This is because stage sets are not
-- algebras (not closed under sup), so it doesn't make sense to use
-- as an assignment. Instead we use T-alg and require explicit proof
-- on the ≈psat case.
lhs' : ∀ (e : E) (ϕ : Assignment T-alg (Ξ e)) → T
lhs' e ϕ = assign T-alg ϕ (Ξ e .lhs)

rhs' : ∀ (e : E) (ϕ : Assignment T-alg (Ξ e)) → T
rhs' e ϕ = assign T-alg ϕ (Ξ e .rhs)

-- Stage-indexed equivalence relation: the quotient relation at each stage.
-- This is built inductively using congruence, equation satisfaction,
-- equivalence relation properties, and weakening.
infixl 3 _⊢_≈ᵇ_
data _⊢_≈ᵇ_ : (α : Z) → D₀ α → D₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  -- Congruence: constructor applications respect equivalence
  ≈pcong : ∀ a μ (f g : ∀ i → D₀ (μ i))
        → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
        → sup (ιˢ a , μ) ⊢ psup a μ f ≈ᵇ psup a μ g

  -- Equation satisfaction: enforce the equations from the signature
  ≈psat : ∀ {α} (e : E) (ϕ : Assignment T-alg (Ξ e))
        → (l≤α : lhs' e ϕ ≤ᵀ α)
        → (r≤α : rhs' e ϕ ≤ᵀ α)
        → α ⊢  (lhs' e ϕ , l≤α)
            ≈ᵇ (rhs' e ϕ , r≤α)

  -- Equivalence relation structure
  ≈prefl : ∀ {α t̂} → α ⊢ t̂ ≈ᵇ t̂
  ≈psym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ ŝ
  ≈ptrans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ û → α ⊢ ŝ ≈ᵇ û

  -- Weakening: equivalences persist across stage inclusions
  ≈pweaken : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : D₀ α}
          → α ⊢ ŝ ≈ᵇ t̂ → β ⊢ pweaken α≤β ŝ ≈ᵇ pweaken α≤β t̂

module _ {ℓW}
  (P : ∀ {α} {s t : D₀ α} → α ⊢ s ≈ᵇ t → Prop ℓW)
  (mcong : ∀ a μ f g (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
          → (∀ i → P (r i))
          → P (≈pcong a μ f g r))
  (msat : ∀ {α} (e : E) ϕ (l≤α : lhs' e ϕ ≤ᵀ α) (r≤α : rhs' e ϕ ≤ᵀ α)
        → P (≈psat {α} e ϕ l≤α r≤α))
  (mrefl : ∀ {α t} → P (≈prefl {α} {t}))
  (msym : ∀ {α s t} (p : α ⊢ s ≈ᵇ t) → P p → P (≈psym p))
  (mtrans : ∀ {α s t u} (p : α ⊢ s ≈ᵇ t) (q : α ⊢ t ≈ᵇ u)
          → P p → P q → P (≈ptrans p q))
  (mweaken : ∀ {α β} (α≤β : α ≤ β) {s t : D₀ α} (p : α ⊢ s ≈ᵇ t)
            → P p → P (≈pweaken α≤β p))
  where
  ≈ᵇ-elim : ∀ {α} {s t : D₀ α} (p : α ⊢ s ≈ᵇ t) → P p
  ≈ᵇ-elim (≈pcong a μ f g r) =
    mcong a μ f g r (λ i → ≈ᵇ-elim (r i))
  ≈ᵇ-elim (≈psat e ϕ l≤α r≤α) =
    msat e ϕ l≤α r≤α
  ≈ᵇ-elim ≈prefl =
    mrefl
  ≈ᵇ-elim (≈psym p) =
    msym p (≈ᵇ-elim p)
  ≈ᵇ-elim (≈ptrans p q) =
    mtrans p q (≈ᵇ-elim p) (≈ᵇ-elim q)
  ≈ᵇ-elim (≈pweaken α≤β p) =
    mweaken α≤β p (≈ᵇ-elim p)

-- Each stage forms a setoid with the stage-indexed equivalence.
-- This gives us a sequence of quotient approximations.
D̃ : (α : Z) → Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D̃ α = record
  { Carrier = D₀ α
  ; _≈_ = α ⊢_≈ᵇ_
  ; isEquivalence = record
    { refl = ≈prefl
    ; sym = ≈psym
    ; trans = ≈ptrans } }

-- The complete diagram: stages connected by weakening morphisms.
-- This forms a cocone over the plump ordinal preorder, and the colimit
-- will give us the final quotient inductive type.
D : Diagram (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D = record
  { D-ob = D̃
  ; D-mor = Hom
  ; D-id = Id
  ; D-comp = Comp }
  where
  -- Morphisms are weakening maps preserving equivalence
  Hom : ∀ {α β} → α ≤ β → ≈.Hom (D̃ α) (D̃ β)
  Hom {α} {β} α≤β = record
    { to = pweaken α≤β
    ; cong = ≈pweaken α≤β }

  -- Identity law: weakening by reflexivity is the identity
  Id : ∀ {α} → (Hom (≤refl α)) ≈h ≈.idHom
  Id {α} {ŝ} = ≈prefl

  -- Composition law: weakening composes correctly
  Comp : ∀ {α β γ} (p : α ≤ β) (q : β ≤ γ) →
      Hom (≤≤ q p) ≈h (Hom q ≈.∘ Hom p)
  Comp {α} {β} {γ} p q {ŝ} =
    ≈pweaken q (≈pweaken p (≈prefl {t̂ = ŝ}))
