module QIT.Examples.Plump.Postulated {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) where

open import QIT.Prelude
open import QIT.Prop
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

-- Z is the raw plump ordinal type (= W Sᶻ Pᶻ), inherited from Plump.
-- The sup constructor on Z comes from W.sup, which Plump re-exports as Z's
-- sole constructor.

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


-- The extensional quotient: two ordinals are identified when they are
-- mutually ≤.  All the ordinal operations and lemmas above work on Z
-- (the raw type); Z/ is provided for use in colimit constructions that
-- need a set-quotient.
Z/ : Set (ℓS ⊔ ℓP)
Z/ = Z̃ /≈

open SetoidQuotient Z̃

join : Z/ → Z/ → Z/
join = rec (λ α → rec (f α) {!!}) {!!}
  where
  f : Z → Z → Z/
  f α β = [ α ∨ᶻ β ]
  f-cong : ∀ {α β γ δ} → α ≤≥ β → γ ≤≥ δ → (α ∨ᶻ γ) ≤≥ (β ∨ᶻ δ)
  f-cong {α} {β} {γ} {δ} (sup≤ p , sup≤ q) (sup≤ r , sup≤ s) = {!!} , {!!}
        

postulate
  sup/ : ⟦ S ◁ P ⟧ Z/ → Z/

_≤/_ : Z/ → Z/ → Prop (ℓS ⊔ ℓP)
_≤/_ = rec₂ {B = Prop (ℓS ⊔ ℓP)} _≤_ ≤-cong
  where
  open Setoid Z̃
  ≤-cong : ∀ {x y z w} → x ≤≥ y → z ≤≥ w → (x ≤ z) ≡ (y ≤ w)
  ≤-cong (x≤y , y≤x) (z≤w , w≤z) =
    propExt ((λ x≤z → ≤≤ z≤w (≤≤ x≤z y≤x))
           , (λ y≤w → ≤≤ w≤z (≤≤ y≤w x≤y)))

_</_ : Z/ → Z/ → Prop (ℓS ⊔ ℓP)
_</_ = rec₂ {B = Prop (ℓS ⊔ ℓP)} _<_ <-cong
  where
  open Setoid Z̃
  <-cong : ∀ {x y z w} → x ≤≥ y → z ≤≥ w → (x < z) ≡ (y < w)
  <-cong (x≤y , y≤x) (z≤w , w≤z) =
    propExt ((λ x<z → ≤< z≤w (<≤ x<z y≤x))
           , (λ y<w → ≤< w≤z (<≤ y<w x≤y)))


-- The well-founded recursion principle on Z, inherited from iswf<.
-- This can be used to build recursive constructions on the raw ordinals
-- that are later quotiented.
open import QIT.Relation.Binary using (WellFounded; Acc; WfRec; acc)

-- iswf</ : WellFounded _</_
-- iswf</ α = acc λ β β<α → p α β (<→≤ β<α)
--   where
--   p : ∀ α β → β ≤ α → Acc _</_ β
--   p (sup (_ , f)) β β≤α = acc q
--     where
--     q : WfRec _<_ (Acc _<_) β
--     q γ γ<β with ≤< β≤α γ<β
--     ... | <sup i γ≤fi = p (f i) γ γ≤fi

