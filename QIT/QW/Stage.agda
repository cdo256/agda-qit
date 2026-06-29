open import QIT.Prelude
open import QIT.Prop
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient
import QIT.Plump.Algebra as Plump

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
  (ZA : Plump.Algebra (sig .Sig.S) (sig .Sig.P))
  where
open Sig sig
open FunExt funExt*


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

module Z = AlgProperties ZA

open Z

-- Diagram is a functor from a preorder category to setoids
Diagram≈ : ∀ ℓD ℓD' → Set (ℓA ⊔ lsuc ℓD ⊔ lsuc ℓD')
Diagram≈ ℓD ℓD' = Functor (PreorderCat Z ≤p) (SetoidCat ℓD ℓD')

Diagram/≈ : ∀ ℓD ℓD' → Set (ℓA ⊔ lsuc ℓD ⊔ lsuc ℓD')
Diagram/≈ ℓD ℓD' = Functor (PreorderCat Z ≤p) (SetCat (ℓD ⊔ ℓD'))

_^_ : ∀ {ℓD ℓD'} → Diagram/≈ ℓD ℓD' → Set ℓD → Diagram/≈ ℓD ℓD'
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
D₀ : (α : Z) → Set (ℓA ⊔ ℓS ⊔ ℓP)
D₀ α = ΣP T (_≤ᵀ α)

-- Constructor for stage elements: build a tree with given shape and children.
-- The ordinal bound is computed from the children's bounds using plump structure.
psup : ∀ a μ (f : ∀ i → D₀ (μ i)) → D₀ (Z.sup (ιₛ a , μ))
psup a μ f = W.sup (a , λ i → ⟨ f i ⟩ᴾ) , sup≤ (λ i → <sup i (f i .snd))

-- Weakening: if α ≤ β then stage α embeds into stage β.
-- This gives the morphisms in our diagram of stages.
pweaken : ∀ {α β} → α ≤ β → D₀ α → D₀ β
pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

-- Ordinal complexity of expressions: measures the "depth" needed to satisfy equations.
-- Variables have minimal complexity ⊥ᶻ, constructors have complexity based on arguments.
ιᵉ : {V : Set ℓV} → Expr V → Z
ιᵉ (varᴱ v) = ⊥ᶻ
ιᵉ (supᴱ s f) = Z.sup (ιₛ s , λ i → ιᵉ (f i))

-- Expression-ordinal comparison: when an expression fits within a stage.
_≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop ℓA
t ≤ᴱ α = ιᵉ t ≤ α

-- Interpretation of equation sides as W-type elements.
-- These functions evaluate expressions in the underlying W-type T.
-- We work in T, requiring proof that the left and right substituted expressions
-- are under the bound α. This is because stage sets are not
-- algebras (not closed under sup), so it doesn't make sense to use
-- as an assignment. Instead we use T-alg and require explicit proof
-- on the ≈psat case.
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
infixl 3 _⊢_≈ᵇ_
data _⊢_≈ᵇ_ : (α : Z) → D₀ α → D₀ α → Prop (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV) where
  -- Congruence: constructor applications respect equivalence
  ≈pcong : ∀ a μ (f g : ∀ i → D₀ (μ i))
        → (r : ∀ i → μ i ⊢ f i ≈ᵇ g i)
        → Z.sup (ιₛ a , μ) ⊢ psup a μ f ≈ᵇ psup a μ g

  -- Equation satisfaction: enforce the equations from the signature
  ≈psat : ∀ {α} (e : E) (ϕ : Assignment T-alg* (Ξ e))
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
D̃ : (α : Z) → Setoid (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D̃ α = record
  { Carrier = D₀ α
  ; _≈_ = α ⊢_≈ᵇ_
  ; isEquivalence = record
    { refl = ≈prefl
    ; sym = ≈psym
    ; trans = ≈ptrans } }

D̃/≈ : Z → Set (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D̃/≈ α = D̃ α /≈

-- The complete diagram: stages connected by weakening morphisms.
-- This forms a cocone over the plump ordinal preorder, and the colimit
-- will give us the final quotient inductive type.
D≈ : Diagram≈ (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
D≈ = record
  { ob = D̃
  ; hom = hom
  ; id = ≈prefl
  ; comp = λ _ _ → ≈prefl
  ; resp = λ _ → ≈prefl }
  module D≈ where
  -- Morphisms are weakening maps preserving equivalence
  hom : ∀ {α β} → Box (α ≤ β) → ≈.Hom (D̃ α) (D̃ β)
  hom {α} {β} (box α≤β) = record
    { to = pweaken α≤β
    ; cong = ≈pweaken α≤β }

module D/≈ where
  module ≤p = Category (PreorderCat Z ≤p)
  module SetoidCat = Category (SetoidCat (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV))
  module SetCat = Category (SetCat (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV))
  open ≡.≡-Reasoning

  sameStage : ∀ {α} {t : T} (p q : t ≤ᵀ α) → D̃ α [ (t , p) ≈ (t , q) ]
  sameStage {α} p q = ≡→≈ (D̃ α) (ΣP≡ _ _ ≡.refl)

  hom : ∀ {α β} → Box (α ≤ β) → D̃ α /≈ → D̃ β /≈
  hom {α} {β} (box α≤β) =
    Qα.rec (λ s → Qβ.[ pweaken α≤β s ])
            (λ p → Qβ.≈[ ≈pweaken α≤β p ])
    where
    module Qα = SQ (D̃ α)
    module Qβ = SQ (D̃ β)

  hom-beta : ∀ {α β} → (p : Box (α ≤ β)) → (s : D₀ α)
            → hom p (D̃ α ⊢[ s ]) ≡ D̃ β ⊢[ pweaken (unbox p) s ]
  hom-beta {α} {β} (box α≤β) s =
    Qα.rec-beta (λ (s : D₀ α) → Qβ.[ pweaken α≤β s ])
    (λ p → Qβ.≈[ ≈pweaken α≤β p ]) s
    where
    module Qα = SQ (D̃ α)
    module Qβ = SQ (D̃ β)

  id : ∀ {α} → hom (≤p.id {α}) ≡h SetCat.id
  id {α} {t̃} = q t̃
    where
    module Qα = SQ (D̃ α)
    q : ∀ t̃ → hom {α} ≤p.id t̃ ≡ SetCat.id {D̃ α /≈} t̃
    q = Qα.elimp (λ t̃ → hom ≤p.id t̃ ≡ SetCat.id t̃)
                  (hom-beta ≤p.id)
  comp : ∀ {α β γ} (f : Box (α ≤ β)) (g : Box (β ≤ γ))
        → hom (g ≤p.∘ f) ≡h (hom g SetCat.∘ hom f)
  comp {α} {β} {γ} (box f) (box g) {t̃} = Qα.elimp _ r t̃
    where
    module Qα = SQ (D̃ α)
    r : (s : D₀ α)
      → hom (box g ≤p.∘ box f) (D̃ α ⊢[ s ])
      ≡ (hom (box g) SetCat.∘ hom (box f)) (D̃ α ⊢[ s ])
    r s = 
      hom (box g ≤p.∘ box f) (D̃ α ⊢[ s ])
        ≡⟨ hom-beta (box (≤≤ g f)) s ⟩
      D̃ γ ⊢[ pweaken (≤≤ g f) s ]
        ≡⟨ ≡.sym (hom-beta (box g) (pweaken f s)) ⟩
      hom (box g) (D̃ β ⊢[ pweaken f s ])
        ≡⟨ ≡.cong (hom (box g)) (≡.sym (hom-beta (box f) s)) ⟩
      hom (box g) (hom (box f) (D̃ α ⊢[ s ])) ∎

  D : Diagram/≈ (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
  D .Functor.ob = D̃/≈
  D .Functor.hom = hom
  D .Functor.id = id
  D .Functor.comp = comp
  D .Functor.resp _ = ≡.refl

  open import QIT.Function.Base
  open import QIT.Set.Bijection

  isInjHom : ∀ {α β} (p : α ≤ β)
            → (∀ {x y} → D̃ β [ pweaken p x ≈ pweaken p y ] → D̃ α [ x ≈ y ])
            → (∀ {x y} → hom (box p) (D̃ α ⊢[ x ]) ≡ hom (box p) (D̃ α ⊢[ y ])
                        → _≡_ {A = D̃ α /≈} (D̃ α ⊢[ x ]) (D̃ α ⊢[ y ]))
  isInjHom {α} {β} α≤β injWeaken {x} {y} q =
    D̃ α ⊢≈[ injWeaken r ]
    where
    module Qα = SQ (D̃ α)
    module Qβ = SQ (D̃ β)

    q' : Qβ.[ pweaken α≤β x ] ≡ Qβ.[ pweaken α≤β y ]
    q' =
      D̃ β ⊢[ pweaken α≤β x ]
        ≡⟨ ≡.sym (hom-beta (box α≤β) x) ⟩
      hom (box α≤β) (D̃ α ⊢[ x ])
        ≡⟨ q ⟩
      hom (box α≤β) (D̃ α ⊢[ y ])
        ≡⟨ hom-beta (box α≤β) y ⟩
      D̃ β ⊢[ pweaken α≤β y ] ∎

    r : D̃ β [ pweaken α≤β x ≈ pweaken α≤β y ]
    r = Qβ.effectiveness _ _ q'

open D/≈ using (D) public
