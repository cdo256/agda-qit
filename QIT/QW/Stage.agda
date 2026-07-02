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
  {ℓZ ℓ< ℓ≤} (Zᴬ : PlumpAlgebra (sig .Sig.S) (sig .Sig.P) ℓZ ℓ< ℓ≤)
  where
open Sig sig
open FunExt funExt*

open import QIT.Plump.Properties Zᴬ as Z

open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base using (_≡h_)
open import QIT.Relation.Subset
open import QIT.Relation.SetQuotient
open import QIT.QW.W S P
open import QIT.Algebra F
open import QIT.Algebra.Lift S P ℓV
open import QIT.Maybe
open import QIT.QW.Equation S P ℓV
open import QIT.Category.Preorder
open import QIT.Category.Setoid
open import QIT.Category.Set
open import QIT.Category.Base hiding (_[_≈_])
open import QIT.Functor.Base
open import QIT.Functor.Properties
import QIT.Setoid.Indexed as Ix
open import QIT.Setoid.Hom 

open SQ

-- Diagram is a functor from a preorder category to setoids
Diagram₀ : ∀ ℓD ℓD' → Set (ℓZ ⊔ ℓ≤ ⊔ lsuc ℓD ⊔ lsuc ℓD')
Diagram₀ ℓD ℓD' =
  Functor (PreorderCat Z ≤p) (SetoidCat ℓD ℓD')

Diagram : ∀ ℓD ℓD' → Set (ℓZ ⊔ ℓ≤ ⊔ lsuc ℓD ⊔ lsuc ℓD')
Diagram ℓD ℓD' =
  Functor (PreorderCat Z ≤p) (SetCat (ℓD ⊔ ℓD'))

_^_ : ∀ {ℓD ℓD'} → Diagram ℓD ℓD' → Set ℓD → Diagram ℓD ℓD'
D ^ X = record
  { ob   = λ α → X → D.ob α
  ; hom  = λ p f x → D.hom p (f x)
  ; id   = funExt λ _ → D.id
  ; comp = λ f g → funExt λ _ → D.comp f g
  ; resp = λ p → funExt λ _ → D.resp p
  }
  where module D = Functor D

open Box

-- Stage α: elements of the underlying W-type bounded by ordinal α.
-- This gives us size-bounded approximations to the final quotient.
S₀ : (α : Z) → Set (ℓ≤ ⊔ ℓS ⊔ ℓP)
S₀ α = ΣP T (_≤ᵀ α)

S-fst : ∀ {α} → S₀ α → T
S-fst = fst
S-snd : ∀ {α} → (t̂ : S₀ α) → S-fst t̂ ≤ᵀ α
S-snd = snd

-- Constructor for stage elements: build a tree with given shape and children.
-- The ordinal bound is computed from the children's bounds using plump structure.
ssup₀ : ∀ a μ (f : ∀ i → S₀ (μ i))
      → S₀ (Z.sup (a , μ))
ssup₀ a μ f = W.sup (a , λ i → ⟨ f i ⟩ᴾ) , sup≤ (λ i → <sup i (f i .snd))

-- Weakening: if α ≤ β then stage α embeds into stage β.
-- This gives the morphisms in our diagram of stages.
dweaken₀ : ∀ {α β} → α ≤ β → S₀ α → S₀ β
dweaken₀ α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

-- Ordinal complexity of expressions: measures the "depth" needed to satisfy equations.
-- Variables have minimal complexity ⊥ᶻ, constructors have complexity based on arguments.
ιᵉ : {V : Set ℓV} → Expr V → Z
ιᵉ (varᴱ v) = ⊥ᶻ
ιᵉ (supᴱ s f) = Z.sup (s , λ i → ιᵉ (f i))

-- Expression-ordinal comparison: when an expression fits within a stage.
_≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop ℓ≤
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

_≈ˢ_ : {α β : Z} → S₀ α → S₀ β → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
(s , _) ≈ˢ (t , _) = s ≈ᵗ t

infix 3 _⊢_≈ᵇ_ _≈ᵗ_ _≈ˢ_

-- Shim
_⊢_≈ᵇ_ : (α : Z) → S₀ α → S₀ α → Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
_ ⊢ ŝ ≈ᵇ t̂ = ŝ ≈ˢ t̂

≈scong : ∀ a μ (f g : ∀ i → S₀ (μ i))
      → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
      → Z.sup (a , μ) ⊢ ssup₀ a μ f ≈ᵇ ssup₀ a μ g
≈scong a _ f g r = ≈tcong a (λ i → f i .fst) (λ i → g i .fst) r

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

S̃ : Z → Setoid (ℓS ⊔ ℓP ⊔ ℓ≤) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
S̃ α = record
  { Carrier = S₀ α
  ; _≈_ = λ ŝ t̂ → ŝ ≈ˢ t̂
  ; isEquivalence = record
    { refl = ≈trefl
    ; sym = ≈tsym
    ; trans = ≈ttrans } }

S̃/ : Z → Set (ℓ≤ ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
S̃/ α = S̃ α /≈

-- Weakening: equivalences persist across stage inclusions
dweaken-cong : ∀ {α β} → (α≤β : α ≤ β) → {ŝ t̂ : S₀ α}
        → ŝ ≈ˢ t̂ → dweaken₀ α≤β ŝ ≈ˢ dweaken₀ α≤β t̂
dweaken-cong _ p = p

dweaken : ∀ {α β} → α ≤ β → ≈.Hom (S̃ α) (S̃ β)
dweaken α≤β = record
  { to = dweaken₀ α≤β
  ; cong = λ {ŝ t̂} → dweaken-cong α≤β {ŝ} {t̂} }

D₀ : Diagram₀ (ℓ≤ ⊔ ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
D₀ = record
  { ob = S̃
  ; hom = λ (box p) → dweaken p
  ; id = ≈trefl
  ; comp = λ _ _ → ≈trefl
  ; resp = λ _ → ≈trefl }

dweaken/ : ∀ {α β} → α ≤ β → S̃ α /≈ → S̃ β /≈
dweaken/ {α} {β} p = rec (S̃ α) (λ s → S̃ β ⊢[ dweaken₀ p s ]) (S̃ β ⊢≈[_])

dweaken-beta : ∀ {α β} → (p : α ≤ β) → (s : S₀ α) → dweaken/ p (S̃ α ⊢[ s ]) ≡ (S̃ β ⊢[ dweaken₀ p s ])
dweaken-beta {α} {β} p s = rec-beta (S̃ α) (λ s → S̃ β ⊢[ dweaken₀ p s ]) (S̃ β ⊢≈[_]) s

module ≤p = Preorder ≤p

id : ∀ {α} → dweaken (≤p.id {α}) ≡h SetCat.id
id {α} {t̃} = q t̃
  where
  module Qα = SetoidQuotient (D̃ α)
  q : ∀ t̃ → hom {α} ≤p.id t̃ ≡ SetCat.id {D̃ α /≈} t̃
  q = Qα.elimp (λ t̃ → hom ≤p.id t̃ ≡ SetCat.id t̃)
                (hom-beta ≤p.id)
comp : ∀ {α β γ} (f : Box (α ≤ β)) (g : Box (β ≤ γ))
    → hom (g ≤p.∘ f) ≡h (hom g SetCat.∘ hom f)
comp {α} {β} {γ} (box f) (box g) {t̃} = Qα.elimp _ r t̃
  where
  module Qα = SetoidQuotient (D̃ α)
  r : (s : S₀ α)
    → hom (box g ≤p.∘ box f) (D̃ α ⊢[ s ])
    ≡ (hom (box g) SetCat.∘ hom (box f)) (D̃ α ⊢[ s ])
  r s = 
    hom (box g ≤p.∘ box f) (D̃ α ⊢[ s ])
      ≡⟨ hom-beta (box (≤≤ g f)) s ⟩
    D̃ γ ⊢[ dweaken₀ (≤≤ g f) s ]
      ≡⟨ ≡.sym (hom-beta (box g) (dweaken₀ f s)) ⟩
    hom (box g) (D̃ β ⊢[ dweaken₀ f s ])
      ≡⟨ ≡.cong (hom (box g)) (≡.sym (hom-beta (box f) s)) ⟩
    hom (box g) (hom (box f) (D̃ α ⊢[ s ])) ∎

open import QIT.Function.Base
open import QIT.Set.Bijection

isInjHom : ∀ {α β} (p : α ≤ β)
        → ∀ {x y} → hom (box p) (D̃ α ⊢[ x ]) ≡ hom (box p) (D̃ α ⊢[ y ])
        → _≡_ {A = D̃ α /≈} (D̃ α ⊢[ x ]) (D̃ α ⊢[ y ])
isInjHom {α} {β} α≤β {x} {y} q =
  Qα.≈[ Qβ.effectiveness _ _ q' ]
  where
  module Qα = SetoidQuotient (D̃ α)
  module Qβ = SetoidQuotient (D̃ β)

  q' : Qβ.[ dweaken₀ α≤β x ] ≡ Qβ.[ dweaken₀ α≤β y ]
  q' =
    D̃ β ⊢[ dweaken₀ α≤β x ]
      ≡⟨ ≡.sym (hom-beta (box α≤β) x) ⟩
    hom (box α≤β) (D̃ α ⊢[ x ])
      ≡⟨ q ⟩
    hom (box α≤β) (D̃ α ⊢[ y ])
      ≡⟨ hom-beta (box α≤β) y ⟩
    D̃ β ⊢[ dweaken₀ α≤β y ] ∎

D/ : Diagram {!!} {!!}
D/ = record
  { ob = S̃/
  ; hom = λ {x} {y} p → {!dweaken-cong!}
  ; id = {!!}
  ; comp = {!!}
  ; resp = {!!} }

-- D̃/≈ : Z → Set (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV ⊔ ℓA)
-- D̃/≈ α = D̃ α /≈

-- -- Morphisms are weakening maps preserving equivalence
-- hom : ∀ {α β} → Box (α ≤ β) → ≈.Hom (D̃ α) (D̃ β)
-- hom {α} {β} (box α≤β) = record
--   { to = dweaken₀ α≤β
--   ; cong = λ z → z }

-- -- TODO: These are now trivial.
-- subst-S₀-fst : ∀ {γ δ} (p : γ ≡ δ) (û : S₀ γ) → D-fst (subst S₀ p û) ≡ D-fst û
-- subst-S₀-fst ≡.refl û = ≡.refl

-- -- The complete diagram: stages connected by weakening morphisms.
-- -- This forms a cocone over the plump ordinal preorder, and the colimit
-- -- will give us the final quotient inductive type.
-- D≈ : Diagram≈ (ℓA ⊔ ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
-- D≈ = record
--   { ob = D̃
--   ; hom = hom
--   ; id = ≈trefl
--   ; comp = λ _ _ → ≈trefl
--   ; resp = λ _ → ≈trefl }


-- -- D : Diagram/≈ (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
-- -- D = record
-- --   { ob = λ α → D̃ α /≈
-- --   ; hom = hom
-- --   ; id = id
-- --   ; comp = comp
-- --   ; resp = λ _ → ≡.refl }
-- --   module D/≈ where
-- --   module ≤p = Category (PreorderCat Z ≤p)
-- --   module SetoidCat = Category (SetoidCat (ℓA ⊔ ℓS ⊔ ℓP) (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV))
-- --   module SetCat = Category (SetCat (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV))
-- --   open ≡.≡-Reasoning

