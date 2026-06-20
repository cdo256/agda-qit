open import QIT.Prelude
open import QIT.Prop
open import QIT.QW.Signature
import QIT.Relation.SetQuotient as QuotRel

-- Define staged construction of quotient W-types using plump ordinals.
-- This builds the quotient in stages indexed by ordinals, ensuring that
-- equations are satisfied at each stage. The construction uses diagrams
-- indexed by the plump ordinal order to control the complexity of terms.
module QIT.QW.Stage {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (propExt : PropExt)
  (sq : QuotRel.SetQuotients)
  (sqe : QuotRel.SetQuotientsElim)
  where
open Sig sig

import QIT.Plump.Algebra as Plump
import QIT.Plump.W.Base as PlumpW
import QIT.Plump.Properties as PlumpP

module ZW = PlumpW S P
module ZAlg = Plump ZW.Sᶻ ZW.Pᶻ
module ZP = PlumpP S P

open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Setoid
open import QIT.Setoid.Quotient propExt sq sqe
module Quot = QuotRel.WithSetQuotients sq sqe
open Quot using ([_]; quot-rec; quot-elimp; quot-rec-beta; quot-rel)
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

module WithZ {ℓA} (ZA : ZAlg.Algebra ℓA) where
  module Z = ZP.AlgProperties ZA

  open ZW using (ιˢ)
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
    ; id   = ≡.funExt λ _ → D.id
    ; comp = λ f g → ≡.funExt λ _ → D.comp f g
    ; resp = λ p → ≡.funExt λ _ → D.resp p
    }
    where module D = Functor D

  open Box

  -- Stage α: elements of the underlying W-type bounded by ordinal α.
  -- This gives us size-bounded approximations to the final quotient.
  D₀ : (α : Z) → Set (ℓA ⊔ ℓS ⊔ ℓP)
  D₀ α = ΣP T (_≤ᵀ α)

  -- Constructor for stage elements: build a tree with given shape and children.
  -- The ordinal bound is computed from the children's bounds using plump structure.
  psup : ∀ a μ (f : ∀ i → D₀ (μ i)) → D₀ (Z.sup (ιˢ a , μ))
  psup a μ f = W.sup (a , λ i → ⟨ f i ⟩ᴾ) , sup≤ (λ i → <sup i (f i .snd))

  -- Weakening: if α ≤ β then stage α embeds into stage β.
  -- This gives the morphisms in our diagram of stages.
  pweaken : ∀ {α β} → α ≤ β → D₀ α → D₀ β
  pweaken α≤β (t , t≤α) = t , ≤≤ α≤β t≤α

  -- Ordinal complexity of expressions: measures the "depth" needed to satisfy equations.
  -- Variables have minimal complexity ⊥ᶻ, constructors have complexity based on arguments.
  ιᵉ : {V : Set ℓV} → Expr V → Z
  ιᵉ (varᴱ v) = ⊥ᶻ
  ιᵉ (supᴱ s f) = Z.sup (ιˢ s , λ i → ιᵉ (f i))

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
          → Z.sup (ιˢ a , μ) ⊢ psup a μ f ≈ᵇ psup a μ g

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

  D : Diagram/≈ (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
  D = record
    { ob = λ α → D̃ α /≈
    ; hom = hom
    ; id = id
    ; comp = comp
    ; resp = λ _ → ≡.refl }
    module D/≈ where
    module ≤p = Category (PreorderCat Z ≤p)
    module SetoidCat = Category (SetoidCat (ℓA ⊔ ℓS ⊔ ℓP) (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV))
    module SetCat = Category (SetCat (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV))
    open ≡.≡-Reasoning

    sameStage : ∀ {α} {t : T} (p q : t ≤ᵀ α) → D̃ α [ (t , p) ≈ (t , q) ]
    sameStage {α} p q = ≡→≈ (D̃ α) (ΣP≡ _ _ ≡.refl)

    hom : ∀ {α β} → Box (α ≤ β) → D̃ α /≈ → D̃ β /≈
    hom {α} {β} (box α≤β) = quot-rec (λ s → [ pweaken α≤β s ])
      λ s t p → quot-rel (pweaken α≤β s) (pweaken α≤β t) (≈pweaken α≤β p)

    id : ∀ {α} → hom (≤p.id {α}) ≡h SetCat.id
    id {α} {t̃} = q t̃
      where
      q : ∀ t̃ → hom {α} ≤p.id t̃ ≡ SetCat.id {D̃ α /≈} t̃
      q = quot-elimp (λ t̃ → hom ≤p.id t̃ ≡ SetCat.id t̃) λ s →
            ≡.trans
              (quot-rec-beta (λ s → [ pweaken (≤refl α) s ])
                             (λ s t p → quot-rel (pweaken (≤refl α) s) (pweaken (≤refl α) t) (≈pweaken (≤refl α) p))
                             s)
              (quot-rel (pweaken (≤refl α) s) s (sameStage _ _))

    comp : ∀ {α β γ} (f : Box (α ≤ β)) (g : Box (β ≤ γ))
         → hom (g ≤p.∘ f) ≡h (hom g SetCat.∘ hom f)
    comp {α} {β} {γ} (box f) (box g) {t̃} = q t̃
      where
      q : (t̃ : D̃ α /≈)
        → hom (box g ≤p.∘ box f) t̃
        ≡ (hom (box g) SetCat.∘ hom (box f)) t̃
      q = quot-elimp _ λ s →
            ≡.trans
              (quot-rec-beta (λ s → [ pweaken (≤≤ g f) s ])
                             (λ s t p → quot-rel (pweaken (≤≤ g f) s) (pweaken (≤≤ g f) t) (≈pweaken (≤≤ g f) p))
                             s)
              (≡.trans
                (quot-rel (pweaken (≤≤ g f) s) (pweaken g (pweaken f s)) (sameStage _ _))
                (≡.sym (≡.trans
                  (≡.cong (hom (box g))
                    (quot-rec-beta (λ s → [ pweaken f s ])
                                   (λ s t p → quot-rel (pweaken f s) (pweaken f t) (≈pweaken f p))
                                   s))
                  (quot-rec-beta (λ s → [ pweaken g s ])
                                 (λ s t p → quot-rel (pweaken g s) (pweaken g t) (≈pweaken g p))
                                 (pweaken f s)))))

    open import QIT.Function.Base
    open import QIT.Set.Bijection

    isInjHom : ∀ {α β} (p : α ≤ β)
             → (∀ {x y} → D̃ β [ pweaken p x ≈ pweaken p y ] → D̃ α [ x ≈ y ])
             → (∀ {x y} → hom (box p) [ x ] ≡ hom (box p) [ y ] → _≡_ {A = D̃ α /≈} [ x ] [ y ])
    isInjHom {α} {β} α≤β injWeaken {x} {y} q =
      quot-rel x y (injWeaken r)
      where
      module Qβ = SetoidQuotient (D̃ β)

      q' : Qβ.[ pweaken α≤β x ] ≡ Qβ.[ pweaken α≤β y ]
      q' =
        ≡.trans
          (≡.sym (quot-rec-beta
            (λ s → [ pweaken α≤β s ])
            (λ s t p → quot-rel (pweaken α≤β s) (pweaken α≤β t) (≈pweaken α≤β p))
            x))
          (≡.trans q
            (quot-rec-beta
              (λ s → [ pweaken α≤β s ])
              (λ s t p → quot-rel (pweaken α≤β s) (pweaken α≤β t) (≈pweaken α≤β p))
              y))

      r : D̃ β [ pweaken α≤β x ≈ pweaken α≤β y ]
      r = Qβ.effectiveness _ _ q'
