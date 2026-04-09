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
  ≤-cong : ∀ {x y z w} → x ≤≥ y → z ≤≥ w → (x ≤ z) ≡ (y ≤ w)
  ≤-cong (x≤y , y≤x) (z≤w , w≤z) =
    propExt ((λ x≤z → ≤≤ z≤w (≤≤ x≤z y≤x))
           , (λ y≤w → ≤≤ w≤z (≤≤ y≤w x≤y)))

_</_ : Z/ → Z/ → Prop (ℓS ⊔ ℓP)
_</_ = rec₂ _<_ <-cong
  where
  open Setoid Z̃
  <-cong : ∀ {x y z w} → x ≤≥ y → z ≤≥ w → (x < z) ≡ (y < w)
  <-cong (x≤y , y≤x) (z≤w , w≤z) =
    propExt ((λ x<z → ≤< z≤w (<≤ x<z y≤x))
           , (λ y<w → ≤< w≤z (<≤ y<w x≤y)))

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

elim≤/ : ∀ {ℓX} (X : Z/ → Z/ → Prop ℓX)
      → ({s : Sᶻ} {f : Pᶻ s → Z/}
         → {α : Z/} (f<α : ∀ i → f i </ α)
         → X (sup/ (s , f)) α)
      → (∀ {α β} → α ≤/ β → X α β)

-- Proof strategy: eliminate β then α using nested elimp (both to Prop
-- targets, so no funExt over Prop-domains is needed).
--
-- When β = [b] and α = [W.sup(s, ξ)]:
--   p : [W.sup(s,ξ)] ≤/ [b]  =  W.sup(s,ξ) ≤ b  (by rec₂ rewrite)
--   r f<α : X (sup/ (s, λi → [ξi])) [b]   (r applied to f<α)
--   sup/-beta s ξ : sup/ (s, λi → [ξi]) ≡ [W.sup(s,ξ)]
--   prop-subst transports to X [W.sup(s,ξ)] [b]
-- Note: f<α : ∀ i → ξ i < b  ≡  ∀ i → [ξi] </ [b]  definitionally.
elim≤/ X r {α} {β} p =
  elimp (λ β → α ≤/ β → X α β)
        (λ b →
          elimp (λ α → α ≤/ [ b ] → X α [ b ])
                (λ { (W.sup (s , ξ)) (sup≤ f<α) →
                      ≡.prop-subst {B = λ z → X z [ b ]} (sup/-beta s ξ) (r f<α) })
                α)
        β p


-- -----------------------------------------------------------------------
-- Derived order lemmas on Z/
--
-- These all follow by using elimp to reduce quotient elements to their
-- representatives, at which point the raw Plump lemmas apply directly
-- (by the quot-rec-beta rewrite, [a] ≤/ [b] = a ≤ b definitionally).
-- -----------------------------------------------------------------------

≤refl/ : ∀ α → α ≤/ α
≤refl/ = elimp (λ α → α ≤/ α) (λ a → ≤refl a)

-- The multi-argument order lemmas cannot be proved by nested elimp in
-- Agda because quot-rec applications are opaque to the unifier when
-- appearing as implicit arguments.  They are postulated here; they
-- follow from the corresponding raw Plump lemmas by the quotient map.
record Transitivity : Set (ℓS ⊔ ℓP) where
  field
    ≤≤/ : {α β γ : Z/} → β ≤/ γ → α ≤/ β → α ≤/ γ
    ≤</ : {α β γ : Z/} → β ≤/ γ → α </ β → α </ γ
    <≤/ : {α β γ : Z/} → β </ γ → α ≤/ β → α </ γ
    <→≤/ : {α β : Z/} → α </ β → α ≤/ β

transitivity : Transitivity
transitivity .Transitivity.≤≤/ {α} {β} {γ} β≤γ α≤β = {!!}
  where open Transitivity transitivity
transitivity .Transitivity.≤</ = {!!}
  where open Transitivity transitivity
transitivity .Transitivity.<≤/ = {!!}
  where open Transitivity transitivity
transitivity .Transitivity.<→≤/ = {!!}
  where open Transitivity transitivity

-- <</ : {α β γ : Z/} → β </ γ → α </ β → α </ γ
-- <</ {α} {β} {γ} β<γ α<β = <≤/ {α} {β} {γ} β<γ (<→≤/ {α} {β} α<β)

-- -- -----------------------------------------------------------------------
-- -- Lifted constructors
-- -- -----------------------------------------------------------------------

-- -- Bottom element
-- ⊥/ : Z/
-- ⊥/ = [ ⊥ᶻ ]

-- -- Successor: well-defined since sucᶻ α = sup(∨ˢ, λ _ → α) is
-- -- congruent w.r.t. ≤≥ by ≤≥-cong.
-- suc/ : Z/ → Z/
-- suc/ = rec (λ α → [ sucᶻ α ])
--            (λ α≤≥β → ≈[ ≤≥-cong ∨ˢ _ _ (λ _ → α≤≥β) ])

-- -- Binary join: well-defined since α ∨ᶻ γ = sup(∨ˢ, [α,γ]) is
-- -- congruent in both arguments by ≤≥-cong.
-- join : Z/ → Z/ → Z/
-- join = rec₂ (λ α β → [ α ∨ᶻ β ])
--             (λ αβ γδ → ≈[ ≤≥-cong ∨ˢ _ _
--               (λ { (lift (inj₁ tt)) → αβ
--                  ; (lift (inj₂ tt)) → γδ }) ])

-- -- Embedding of base trees
-- ι/ : W S P → Z/
-- ι/ t = [ ιᶻ t ]

-- -- -----------------------------------------------------------------------
-- -- Axioms for sup/
-- --
-- -- These mirror the sup≤ and <sup constructors for the raw type.
-- -- They cannot be derived without knowing how sup/ acts on elements;
-- -- we postulate them as the interface of the extensional sup.
-- -- -----------------------------------------------------------------------

-- postulate
--   sup≤/ : {s : S} {f : P s → Z/} {α : Z/}
--         → (∀ i → f i </ α)
--         → sup/ (s , f) ≤/ α

--   <sup/ : {s : S} {f : P s → Z/} (i : P s) {α : Z/}
--         → α ≤/ f i
--         → α </ sup/ (s , f)

-- -- -----------------------------------------------------------------------
-- -- Derived order lemmas involving the lifted constructors
-- -- -----------------------------------------------------------------------

-- -- Each child of sup/(s, f) is strictly below it.
-- child≤/ : (s : S) (f : P s → Z/) (i : P s) → f i ≤/ sup/ (s , f)
-- child≤/ s f i = <→≤/ {f i} {sup/ (s , f)} (<sup/ {s} {f} i {f i} (≤refl/ (f i)))

-- -- Congruence: pointwise ≤/ implies ≤/ on sup/.
-- ≤/cong : (s : S) (μ τ : P s → Z/) → (∀ i → μ i ≤/ τ i) → sup/ (s , μ) ≤/ sup/ (s , τ)
-- ≤/cong s μ τ r = sup≤/ {s} {μ} {sup/ (s , τ)} (λ i → <sup/ {s} {τ} i {μ i} (r i))

-- -- α </ suc/ α (the successor is strictly above α).
-- <sucᶻ/ : ∀ α → α </ suc/ α
-- <sucᶻ/ = elimp (λ α → α </ suc/ α) <sucᶻ

-- -- Helper: α is strictly below any sup/ node with shape s when P s is inhabited.
-- <sup/ᶻ : ∀ {s : S} (α : Z/) → ∥ P s ∥ → α </ sup/ (s , λ _ → α)
-- <sup/ᶻ {s} α ∣ i ∣ = <sup/ {s} {λ _ → α} i {α} (≤refl/ α)

-- -- Join inequalities
-- -- Join inequalities: same opaqueness issue for multi-arg cases;
-- -- postulate those, derive the ≤/ ones from <→≤/.
-- join-l< : {α β : Z/} → α </ join α β
-- join-l< {α} {β} = {!!}
--   where
--   w : α </ sup/ ({!∨ˢ!} , {!!})
--   w = <sup/ {!rec-beta!} ≤refl/
-- postulate
--   join-r< : {α β : Z/} → β </ join α β
--   join≤/  : {α β γ : Z/} → α </ γ → β </ γ → join α β ≤/ γ
--   join-flip/ : {α β : Z/} → join β α ≤/ join α β

-- join-l : {α β : Z/} → α ≤/ join α β
-- join-l {α} {β} = <→≤/ {α} {join α β} (join-l< {α} {β})

-- join-r : {α β : Z/} → β ≤/ join α β
-- join-r {α} {β} = <→≤/ {β} {join α β} (join-r< {α} {β})

-- -- -----------------------------------------------------------------------
-- -- Preorder structure on Z/
-- -- -----------------------------------------------------------------------

-- open import QIT.Relation.Binary using (IsPreorder; Preorder; WellFounded; Acc; WfRec; acc)

-- isPreorder-≤/ : IsPreorder _≤/_
-- isPreorder-≤/ = record
--   { refl  = λ {x} → ≤refl/ x
--   ; trans = λ {x} {y} {z} p q → ≤≤/ {x} {y} {z} q p }

-- ≤p/ : Preorder Z/ _
-- ≤p/ = _≤/_ , isPreorder-≤/

-- -- Well-foundedness of _</_ on Z/.
-- -- This requires induction on the quotient type and so is postulated.
-- postulate
--   iswf</ : WellFounded _</_

-- -- -----------------------------------------------------------------------
-- -- Effectiveness: the quotient is effective
-- -- -----------------------------------------------------------------------

-- effectiveness/ : ∀ α β → [ α ] ≡ [ β ] → α ≤≥ β
-- effectiveness/ = effectiveness
