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
module QIT.QW.Stage
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

open import QIT.Plump.Properties Zᴬ 
open PlumpAlgebra Zᴬ renaming (sup to supᶻ)

import QIT.Setoid.Indexed as Ix
open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Algebra F
open import QIT.Algebra.Lift S P ℓV
open import QIT.QW.Equation S P ℓV
open import QIT.QW.W S P
open import QIT.Setoid
import QIT.Setoid.Indexed as Ix

open ≈.SQ

-- Stage α: elements of the underlying W-type bounded by ordinal α.
-- This gives us size-bounded approximations to the final quotient.
S₀ : (α : Z) → Set (ℓS ⊔ ℓP)
S₀ α = ΣP T (_≤ᵀ α)

-- Constructor for stage elements: build a tree with given shape and children.
-- The ordinal bound is computed from the children's bounds using plump structure.
ssup₀ : ∀ a μ (f : ∀ i → S₀ (μ i))
      → S₀ (supᶻ (a , μ))
ssup₀ a μ f = W.sup (a , λ i → ⟨ f i ⟩ᴾ) , sup≤ (λ i → <sup i (f i .snd))

-- Weakening: if α ≤ β then stage α embeds into stage β.
-- This gives the morphisms in our diagram of stages.
dweaken₀ : ∀ {α β} → α ≤ β → S₀ α → S₀ β
dweaken₀ α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

-- Ordinal complexity of expressions: measures the "depth" needed to satisfy equations.
-- Variables have minimal complexity ⊥ᶻ, constructors have complexity based on arguments.
ιᵉ : {V : Set ℓV} → Expr V → Z
ιᵉ (varᴱ v) = ⊥ᶻ
ιᵉ (supᴱ s f) = supᶻ (s , λ i → ιᵉ (f i))

-- Expression-ordinal comparison: when an expression fits within a stage.
_≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop (ℓS ⊔ ℓP)
t ≤ᴱ α = ιᵉ t ≤ α

-- Interpretation of equation sides as W-type elements.
-- These functions evaluate expressions in the underlying W-type T.
-- We work in T, requiring proof that the left and right substituted expressions
-- are under the bound α. This is because stage sets are not
-- algebras (not closed under sup), so it doesn't make sense to use
-- as an assignment. Instead we use T-alg and require explicit proof
-- on the ≈dsat case.
-- Lift T-alg to the higher universe levels needed in this module
T-alg* : Algebra
T-alg* = LiftAlgebra T-alg

lhs' : ∀ (e : E) (ϕ : Assignment T-alg* (Ξ e)) → T
lhs' e ϕ = lower (assign T-alg* ϕ (Ξ e .lhs))

rhs' : ∀ (e : E) (ϕ : Assignment T-alg* (Ξ e)) → T
rhs' e ϕ = lower (assign T-alg* ϕ (Ξ e .rhs))

-- Stage-indexed equivalence relation: the quotient relation at each stage.
-- This is built inductively using congruence, equation satisfaction,
-- equivalence relation properties, and weakening.

data _≈ᵗ_ : T → T → Prop (ℓS ⊔ ℓP ⊔ ℓV ⊔ ℓE) where
  -- Congruence: constructor applications respect equivalence
  ≈tcong : ∀ a (f g : (i : P a) → T)
        → (r : ∀ i → f i ≈ᵗ g i)
        → W.sup (a , f) ≈ᵗ W.sup (a , g)

  -- Equation satisfaction: enforce the equations from the signature
  ≈tsat : ∀ (e : E) (ϕ : Assignment T-alg* (Ξ e))
        → lhs' e ϕ ≈ᵗ rhs' e ϕ

  -- Equivalence relation structure
  ≈trefl : ∀ {t} → t ≈ᵗ t
  ≈tsym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈ttrans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

T̃ : Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
T̃ = record
  { Carrier = T
  ; _≈_ = _≈ᵗ_
  ; isEquivalence = record
    { refl = ≈trefl
    ; sym = ≈tsym
    ; trans = ≈ttrans } }

_≈ˢ_ : {α β : Z} → S₀ α → S₀ β → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
(s , _) ≈ˢ (t , _) = s ≈ᵗ t

infix 3 _⊢_≈ᵇ_ _≈ᵗ_ _≈ˢ_

-- Shim
_⊢_≈ᵇ_ : (α : Z) → S₀ α → S₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
_ ⊢ ŝ ≈ᵇ t̂ = ŝ ≈ˢ t̂

≈scong : ∀ a μ (f g : ∀ i → S₀ (μ i))
      → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
      → supᶻ (a , μ) ⊢ ssup₀ a μ f ≈ᵇ ssup₀ a μ g
≈scong a _ f g r = ≈tcong a (λ i → ⟨ f i ⟩ᴾ) (λ i → ⟨ g i ⟩ᴾ) r

-- Equation satisfaction: enforce the equations from the signature
≈ssat : ∀ (e : E) (ϕ : Assignment T-alg* (Ξ e))
      → lhs' e ϕ ≈ᵗ rhs' e ϕ
≈ssat e ϕ = ≈tsat e ϕ

-- Equivalence relation structure
≈srefl : ∀ {α t̂} → α ⊢ t̂ ≈ᵇ t̂
≈srefl = ≈trefl
≈ssym : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ ŝ
≈ssym = ≈tsym
≈strans : ∀ {α ŝ t̂ û} → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ t̂ ≈ᵇ û → α ⊢ ŝ ≈ᵇ û
≈strans = ≈ttrans

S̃ : Z → Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
S̃ α = record
  { Carrier = S₀ α
  ; _≈_ = λ ŝ t̂ → ŝ ≈ˢ t̂
  ; isEquivalence = record
    { refl = ≈trefl
    ; sym = ≈tsym
    ; trans = ≈ttrans } }

S̃ᶜ : Ix.Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
S̃ᶜ = record
  { I = Z
  ; A = S₀
  ; R = λ _ _ ŝ t̂ → ŝ ≈ˢ t̂
  ; isEquivalence = record
    { refl = ≈trefl
    ; sym = ≈tsym
    ; trans = ≈ttrans } }

open import QIT.Setoid.IndexedQuotient

S̃ᶜ/ : Set (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
S̃ᶜ/ = S̃ᶜ /≈ᴵ

S̃/ : Z → Set (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
S̃/ α = S̃ α /≈

-- Weakening: equivalences persist across stage inclusions
dweaken-cong : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : S₀ α}
        → ŝ ≈ˢ t̂ → dweaken₀ α≤β ŝ ≈ˢ dweaken₀ α≤β t̂
dweaken-cong _ p = p

dweaken : ∀ {α β} → α ≤ β → ≈.Hom (S̃ α) (S̃ β)
dweaken α≤β = record
  { to = dweaken₀ α≤β
  ; cong = λ {ŝ t̂} → dweaken-cong α≤β {ŝ} {t̂} }

dweaken/ : ∀ {α β} → α ≤ β → S̃ α /≈ → S̃ β /≈
dweaken/ {α} {β} p = rec (S̃ α) (λ s → S̃ β ⊢[ dweaken₀ p s ]) (S̃ β ⊢≈[_])

dweaken-beta : ∀ {α β} → (p : α ≤ β) → (s : S₀ α) → dweaken/ p (S̃ α ⊢[ s ]) ≡ (S̃ β ⊢[ dweaken₀ p s ])
dweaken-beta {α} {β} p s = rec-beta (S̃ α) (λ s → S̃ β ⊢[ dweaken₀ p s ]) (S̃ β ⊢≈[_]) s

subst-S₀-fst : ∀ {γ δ} (p : γ ≡ δ) (û : S₀ γ) → ⟨ subst S₀ p û ⟩ᴾ ≡ ⟨ û ⟩ᴾ
subst-S₀-fst {γ} ≡.refl û = ≡.refl

subst-quot-S
  : ∀ {α β} → (p : α ≡ β) (x : S₀ α)
  → S̃ β ⊢[ subst S₀ p x ]
  ≡ subst S̃/ p (S̃ α ⊢[ x ])
subst-quot-S ≡.refl x = ≡.refl
