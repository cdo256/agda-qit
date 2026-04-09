module QIT.Examples.Plump.Postulated {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.Logic
import QIT.Container.Base as W
open W hiding (sup)
open import QIT.Setoid
open import QIT.Setoid.Quotient

import QIT.Relation.Plump S P as Plump

-- Open everything from Plump so the raw ordinal arithmetic is available
-- directly, without needing to pattern-match on a quotient.
open Plump public
  using ( Z ; Sᶻ ; Pᶻ ; ιˢ ; ∨ˢ ; ⊥ˢ
        ; ⊥ᶻ ; sucᶻ ; _∨ᶻ_ ; ιᶻ
        ; _≤_ ; _<_ ; sup≤ ; <sup
        ; ≤refl ; ≤≤ ; ≤< ; <≤
        ; <→≤ ; << ; <supᶻ ; <sucᶻ
        ; _<ᵀ_ ; _≤ᵀ_
        ; child≤ ; iswf< ; isPreorder-≤ ; ≤p
        ; _⊆_ ; _⊇_ ; ⊆→≤ ; ≤→⊆ ; ≤→⊇
        ; _≤≥_ ; _⊆⊇_ ; isQuasiExtensionalZ
        ; ≤cong
        ; ≤≥-refl ; ≤≥-sym ; ≤≥-trans ; ≤≥-cong
        ; ∨ᶻ-l< ; ∨ᶻ-r< ; ∨ᶻ-l ; ∨ᶻ-r ; ∨ᶻ-flip ; ∨ᶻ≤
        ; sup≤sup ; ≡→≤ )

-- -----------------------------------------------------------------------
-- Setoid and quotient structures
--
-- Z̃ equips the raw type with the bisimilarity equivalence (mutual ≤),
-- giving a setoid of "intensional" plump ordinals.
-- Z/ is the corresponding quotient — the type of extensional ordinals
-- in which mutually ≤ elements are identified.
-- -----------------------------------------------------------------------

Z̃ : Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)
Z̃ = record
  { Carrier       = Z
  ; _≈_           = _≤≥_
  ; isEquivalence = record
    { refl  = ≤≥-refl
    ; sym   = ≤≥-sym
    ; trans = ≤≥-trans } }

Z/ : Set (ℓS ⊔ ℓP)
Z/ = Z̃ /≈

open SetoidQuotient Z̃

-- The sup constructor for the original signature.
-- This requires AC in general (to choose representatives of the children
-- in Z/) so we postulate it as an axiom.
postulate
  sup/ : ⟦ Sᶻ ◁ Pᶻ ⟧ Z/ → Z/
  -- Computation rule: sup/ reduces to the quotient injection when all
  -- children are already representatives.  This is the key axiom that
  -- connects the postulated sup/ to the underlying W-type constructor,
  -- and is essential for any elimination principle over ≤/.
  sup/-beta : ∀ (s : Sᶻ) (ξ : Pᶻ s → Z) → sup/ (s , λ i → [ ξ i ]) ≡ [ W.sup (s , ξ) ]

-- -----------------------------------------------------------------------
-- Lifted order relations
--
-- _≤/_ and _</_ are the images of _≤_ and _<_ on the quotient.
-- They are well-defined because ≤ and < are preserved by ≤≥-bisimilarity.
-- -----------------------------------------------------------------------

_≤/_ : Z/ → Z/ → Prop (ℓS ⊔ ℓP)
_≤/_ = rec₂ _≤_ ≤-cong
  where
  open Setoid Z̃
  ≤-cong : ∀ {α β γ δ} → α ≤≥ β → γ ≤≥ δ → (α ≤ γ) ≡ (β ≤ δ)
  ≤-cong (α≤β , β≤α) (γ≤δ , δ≤γ) =
    propExt ((λ α≤γ → ≤≤ γ≤δ (≤≤ α≤γ β≤α))
           , (λ β≤δ → ≤≤ δ≤γ (≤≤ β≤δ α≤β)))

_</_ : Z/ → Z/ → Prop (ℓS ⊔ ℓP)
_</_ = rec₂ _<_ <-cong
  where
  open Setoid Z̃
  <-cong : ∀ {α β γ δ} → α ≤≥ β → γ ≤≥ δ → (α < γ) ≡ (β < δ)
  <-cong (α≤β , β≤α) (γ≤δ , δ≤γ) =
    propExt ((λ α<γ → ≤< γ≤δ (<≤ α<γ β≤α))
           , (λ β<δ → ≤< δ≤γ (<≤ β<δ α≤β)))

elim≤/ : ∀ {ℓX} (X : Z/ → Z/ → Prop ℓX)
      → ({s : Sᶻ} {f : Pᶻ s → Z/}
         → {α : Z/} (f<α : ∀ i → f i </ α)
         → X (sup/ (s , f)) α)
      → (∀ {α β} → α ≤/ β → X α β)
elim≤/ X r {α} {β} p =
  elimp (λ β → α ≤/ β → X α β)
        (λ b →
          elimp (λ α → α ≤/ [ b ] → X α [ b ])
                (λ { (W.sup (s , ξ)) (sup≤ f<α) →
                      ≡.prop-subst {B = λ z → X z [ b ]} (sup/-beta s ξ) (r f<α) })
                α)
        β p

elim</ : ∀ {ℓX} (X : Z/ → Z/ → Prop ℓX)
      → ({s : Sᶻ} {f : Pᶻ s → Z/}
         → (i : Pᶻ s) → {α : Z/} → α ≤/ f i
         → X α (sup/ (s , f)))
      → (∀ {α β} → α </ β → X α β)
elim</ X r {α} {β} p =
  elimp (λ β → α </ β → X α β)
        (λ { (W.sup (s , ξ)) →
          elimp (λ α → α </ [ W.sup (s , ξ) ] → X α [ W.sup (s , ξ) ])
                (λ { a (<sup i a≤ξi) →
                      ≡.prop-subst {B = λ z → X [ a ] z} (sup/-beta s ξ) (r i a≤ξi) })
                α })
        β p

-- -----------------------------------------------------------------------
-- Generating rules for sup/ on the ordering.
--
-- These are the quotient analogues of the sup≤ and <sup constructors.
-- They cannot be derived from sup/-beta alone for a general
-- f : Pᶻ s → Z/ (that would require knowing a representative for each
-- child), so we postulate them as part of the interface of sup/.
-- -----------------------------------------------------------------------
postulate
  sup≤/ : {s : Sᶻ} {f : Pᶻ s → Z/} {α : Z/}
        → (∀ i → f i </ α)
        → sup/ (s , f) ≤/ α

  <sup/ : {s : Sᶻ} {f : Pᶻ s → Z/}
        → (i : Pᶻ s) → {α : Z/}
        → α ≤/ f i
        → α </ sup/ (s , f)

-- -----------------------------------------------------------------------
-- Derived order lemmas on Z/
--
-- The reflexivity proof is a single elimp and needs no eliminator.
-- The transitivity lemmas mirror Plump.agda exactly, replacing each
-- pattern match on a constructor with the corresponding eliminator:
--
--   sup≤ / sup≤/   ←→   elim≤/
--   <sup  / <sup/  ←→   elim</
--
-- Termination: these are structurally recursive on the sizes of the
-- proof witnesses (which are raw Plump ordinals), but establishing
-- this formally for Agda's termination checker is deferred.
-- -----------------------------------------------------------------------

≤refl/ : ∀ α → α ≤/ α
≤refl/ = elimp (λ α → α ≤/ α) (λ a → ≤refl a)

-- Transitivity lemmas for ≤/ and </, mirroring Plump.agda.
-- Each proof eliminates all three quotient arguments to representatives
-- using nested elimp, then applies the corresponding raw Plump lemma
-- with explicit implicit arguments.  Because no quotient-level mutual
-- recursion occurs, no {-# TERMINATING #-} pragma is needed.

-- ≤≤ β≤γ (sup≤ f<β) = sup≤ (λ i → ≤< β≤γ (f<β i))
≤≤/ : {α β γ : Z/} → β ≤/ γ → α ≤/ β → α ≤/ γ
≤≤/ {α = α} {β = β} {γ = γ} β≤γ α≤β =
  elimp (λ γ → β ≤/ γ → α ≤/ β → α ≤/ γ) (λ c →
  elimp (λ β → β ≤/ [ c ] → α ≤/ β → α ≤/ [ c ]) (λ b →
  elimp (λ α → [ b ] ≤/ [ c ] → α ≤/ [ b ] → α ≤/ [ c ])
        (λ a b≤c a≤b → ≤≤ {a} {b} {c} b≤c a≤b)
        α) β) γ β≤γ α≤β

-- ≤< (sup≤ f<γ) (<sup i α≤fi) = <≤ (f<γ i) α≤fi
≤</ : {α β γ : Z/} → β ≤/ γ → α </ β → α </ γ
≤</ {α = α} {β = β} {γ = γ} β≤γ α<β =
  elimp (λ γ → β ≤/ γ → α </ β → α </ γ) (λ c →
  elimp (λ β → β ≤/ [ c ] → α </ β → α </ [ c ]) (λ b →
  elimp (λ α → [ b ] ≤/ [ c ] → α </ [ b ] → α </ [ c ])
        (λ a b≤c a<b → ≤< {a} {b} {c} b≤c a<b)
        α) β) γ β≤γ α<β

-- <≤ (<sup i α≤fi) α≤β = <sup i (≤≤ α≤fi α≤β)
<≤/ : {α β γ : Z/} → β </ γ → α ≤/ β → α </ γ
<≤/ {α = α} {β = β} {γ = γ} β<γ α≤β =
  elimp (λ γ → β </ γ → α ≤/ β → α </ γ) (λ c →
  elimp (λ β → β </ [ c ] → α ≤/ β → α </ [ c ]) (λ b →
  elimp (λ α → [ b ] </ [ c ] → α ≤/ [ b ] → α </ [ c ])
        (λ a b<c a≤b → <≤ {a} {b} {c} b<c a≤b)
        α) β) γ β<γ α≤β

-- <→≤ (<sup i (sup≤ f<fi)) = sup≤ (λ j → <sup i (<→≤ (f<fi j)))
<→≤/ : {α β : Z/} → α </ β → α ≤/ β
<→≤/ {α = α} {β = β} α<β =
  elimp (λ β → α </ β → α ≤/ β) (λ b →
  elimp (λ α → α </ [ b ] → α ≤/ [ b ])
        (λ a a<b → <→≤ {a} {b} a<b)
        α) β α<β

<</ : {α β γ : Z/} → β </ γ → α </ β → α </ γ
<</ {α} {β} {γ} β<γ α<β = <≤/  {α} {β} {γ} β<γ (<→≤/ {α} {β} α<β)

-- -----------------------------------------------------------------------
-- Lifted constructors
-- -----------------------------------------------------------------------

-- Bottom element
⊥/ : Z/
⊥/ = [ ⊥ᶻ ]

_∨ᶻ/_ : {!Z/ → Z/!}

-- Successor: well-defined since sucᶻ α = sup(∨ˢ, λ _ → α) is
-- congruent w.r.t. ≤≥ by ≤≥-cong.
suc/ : Z/ → Z/
suc/ = rec (λ α → [ sucᶻ α ])
           (λ α≤≥β → ≈[ ≤≥-cong ∨ˢ _ _ (λ _ → α≤≥β) ])

-- Binary join: well-defined since α ∨ᶻ γ = sup(∨ˢ, [α,γ]) is
-- congruent in both arguments by ≤≥-cong.
join : Z/ → Z/ → Z/
join = rec₂ (λ α β → [ α ∨ᶻ β ])
            (λ αβ γδ → ≈[ {!≤≥-cong ∨ˢ _ _
              (λ { (lift (inj₁ tt)) → αβ
                 ; (lift (inj₂ tt)) → γδ })!} ])

-- Embedding of base trees
ι/ : W S P → Z/
ι/ t = [ ιᶻ t ]

-- -----------------------------------------------------------------------
-- Derived order lemmas involving the lifted constructors
-- -----------------------------------------------------------------------

-- Each child of sup/(s, ξ) is strictly below it.
child≤/ : (s : Sᶻ) (ξ : Pᶻ s → Z/) (i : Pᶻ s) → ξ i ≤/ sup/ (s , ξ)
child≤/ s ξ i = <→≤/ {ξ i} {sup/ (s , ξ)} (<sup/ {s} {ξ} i {ξ i} (≤refl/ (ξ i)))

-- Congruence: pointwise ≤/ implies ≤/ on sup/.
≤/cong : (s : Sᶻ) (μ τ : Pᶻ s → Z/) → (∀ i → μ i ≤/ τ i) → sup/ (s , μ) ≤/ sup/ (s , τ)
≤/cong s μ τ r = sup≤/ {s} {μ} {sup/ (s , τ)} (λ i → <sup/ {s} {τ} i {μ i} (r i))

-- α </ suc/ α (the successor is strictly above α).
<sucᶻ/ : ∀ α → α </ suc/ α
<sucᶻ/ = elimp (λ α → α </ suc/ α) <sucᶻ

-- Helper: α is strictly below any sup/ node with shape s when P s is inhabited.
<sup/ᶻ : ∀ {s : Sᶻ} (α : Z/) → ∥ Pᶻ s ∥ → α </ sup/ (s , λ _ → α)
<sup/ᶻ {s} α ∣ i ∣ = <sup/ {s} {λ _ → α} i {α} (≤refl/ α)

-- Join inequalities
-- Join inequalities: same opaqueness issue for multi-arg cases;
-- postulate those, derive the ≤/ ones from <→≤/.
join-l< : {α β : Z/} → α </ join α β
join-l< {α} {β} = {!!}
  where
  w : α </ sup/ (∨ˢ , {!!})
  w = <sup/ {!rec-beta!} ≤refl/
postulate
  join-r< : {α β : Z/} → β </ join α β
  join≤/  : {α β γ : Z/} → α </ γ → β </ γ → join α β ≤/ γ
  join-flip/ : {α β : Z/} → join β α ≤/ join α β

join-l : {α β : Z/} → α ≤/ join α β
join-l {α} {β} = <→≤/ {α} {join α β} (join-l< {α} {β})

join-r : {α β : Z/} → β ≤/ join α β
join-r {α} {β} = <→≤/ {β} {join α β} (join-r< {α} {β})

-- -----------------------------------------------------------------------
-- Preorder structure on Z/
-- -----------------------------------------------------------------------

open import QIT.Relation.Binary using (IsPreorder; Preorder; WellFounded; Acc; WfRec; acc)

isPreorder-≤/ : IsPreorder _≤/_
isPreorder-≤/ = record
  { refl  = λ {x} → ≤refl/ x
  ; trans = λ {x} {y} {z} p q → ≤≤/ {x} {y} {z} q p }

≤p/ : Preorder Z/ _
≤p/ = _≤/_ , isPreorder-≤/

-- Well-foundedness of _</_ on Z/.
-- This requires induction on the quotient type and so is postulated.
postulate
  iswf</ : WellFounded _</_

-- -----------------------------------------------------------------------
-- Effectiveness: the quotient is effective
-- -----------------------------------------------------------------------

effectiveness/ : ∀ α β → [ α ] ≡ [ β ] → α ≤≥ β
effectiveness/ = effectiveness
