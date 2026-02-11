open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid.Base
open import QIT.Setoid.Hom

-- Define isomorphisms between setoids: bijective homomorphisms with
-- inverse operations. An isomorphism witnesses that two setoids are
-- "essentially the same" - they have the same structure up to renaming.
module QIT.Setoid.Iso where

-- An isomorphism between setoids S and T consists of a pair of functions
-- that are mutual inverses and both preserve equivalence relations.
-- This is stronger than just having bijective homomorphisms: we need
-- explicit inverse functions with proof that they cancel out.
record Iso {ℓ} {ℓ'} (S T : Setoid ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  module S = Setoid S
  module T = Setoid T
  field
    -- Forward direction: S → T
    ⟦_⟧ : S.Carrier → T.Carrier
    -- Backward direction: T → S
    ⟦_⟧⁻¹ : T.Carrier → S.Carrier
    -- Both directions preserve equivalence
    cong : ∀ {x y} → x S.≈ y → ⟦ x ⟧ T.≈ ⟦ y ⟧
    cong⁻¹ : ∀ {x y} → x T.≈ y → ⟦ x ⟧⁻¹ S.≈ ⟦ y ⟧⁻¹
    -- The functions are mutual inverses (up to equivalence)
    linv : ∀ y → ⟦ ⟦ y ⟧⁻¹ ⟧ T.≈ y
    rinv : ∀ x → ⟦ ⟦ x ⟧ ⟧⁻¹ S.≈ x

-- Flip an isomorphism: if S ≅ T then T ≅ S.
-- Simply swaps the forward/backward directions and left/right inverses.
IsoFlip : ∀ {ℓ ℓ'} → {S T : Setoid ℓ ℓ'} → Iso S T → Iso T S
IsoFlip f = record
  { ⟦_⟧ = ⟦_⟧⁻¹
  ; ⟦_⟧⁻¹ = ⟦_⟧
  ; cong = cong⁻¹
  ; cong⁻¹ = cong
  ; linv = rinv
  ; rinv = linv
  }
  where open Iso f

-- Setoid isomorphism relation: truncated to ensure it's a proposition.
-- Two setoids are isomorphic if there exists an isomorphism between them.
_≅_ : ∀ {ℓ ℓ'} → BinaryRel (Setoid ℓ ℓ') (ℓ ⊔ ℓ')
S ≅ T = ∥ Iso S T ∥

-- Prove that ≅ is an equivalence relation, making setoids form a setoid
-- under isomorphism. This is the "setoid of setoids" construction.
module _ {ℓ ℓ'} where
  isEquivalenceIso : IsEquivalence (_≅_ {ℓ} {ℓ'})
  isEquivalenceIso = record
    { refl = isReflexive
    ; sym = isSymmetric
    ; trans = isTransitive
    }
    where
    -- Every setoid is isomorphic to itself via identity functions
    isReflexive : Reflexive (_≅_ {ℓ} {ℓ'})
    isReflexive {S} = ∣ S~S ∣
      where
      module S = Setoid S
      S~S : Iso S S
      S~S = record
        { ⟦_⟧ = λ x → x
        ; ⟦_⟧⁻¹ = λ x → x
        ; cong = λ p → p
        ; cong⁻¹ = λ p → p
        ; linv = λ _ → S.refl
        ; rinv = λ _ → S.refl
        }

    -- If S ≅ T then T ≅ S by flipping the isomorphism
    isSymmetric : Symmetric (_≅_ {ℓ} {ℓ'})
    isSymmetric {S} {T} ∣ p ∣ = ∣ q ∣
      where
      module S = Setoid S
      module T = Setoid T
      module p = Iso p
      q : Iso T S
      q = record
        { ⟦_⟧ = p.⟦_⟧⁻¹
        ; ⟦_⟧⁻¹ = p.⟦_⟧
        ; cong = p.cong⁻¹
        ; cong⁻¹ = p.cong
        ; linv = p.rinv
        ; rinv = p.linv
        }

    -- Composition of isomorphisms: if S ≅ T and T ≅ U then S ≅ U
    isTransitive : Transitive (Trunc₂ (Iso {ℓ} {ℓ'}))
    isTransitive {S} {T} {U} ∣ p ∣ ∣ q ∣ = ∣ r ∣
      where
      module S = Setoid S
      module T = Setoid T
      module U = Setoid U
      module p = Iso p
      module q = Iso q
      r : Iso S U
      r = record
        { ⟦_⟧ = λ z → q.⟦ p.⟦ z ⟧ ⟧
        ; ⟦_⟧⁻¹ = λ z → p.⟦ q.⟦ z ⟧⁻¹ ⟧⁻¹
        ; cong = λ z → q.cong (p.cong z)
        ; cong⁻¹ = λ z → p.cong⁻¹ (q.cong⁻¹ z)
        ; linv = λ y → U.trans (q.cong (p.linv q.⟦ y ⟧⁻¹)) (q.linv y)
        ; rinv = λ x → S.trans (p.cong⁻¹ (q.rinv p.⟦ x ⟧)) (p.rinv x)
        }

  -- The setoid of setoids: setoids form a setoid under isomorphism
  SetoidSetoid : Setoid (lsuc ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  SetoidSetoid = record
    { Carrier = Setoid ℓ ℓ'
    ; _≈_ = _≅_
    ; isEquivalence = isEquivalenceIso
    }
