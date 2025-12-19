{-# OPTIONS --type-in-type #-}
module Setoid.Iso where

open import Prelude
open import Equivalence
open import Data.Product
open import Setoid.Base
open import Setoid.Hom
 
private
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level
  ℓ = lzero
  ℓ' = lzero
  ℓ'' = lzero
  ℓ''' = lzero
  ℓ'''' = lzero


record Iso {ℓ} {ℓ'} (S T : Setoid ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  module S = Setoid S
  module T = Setoid T
  field
    ⟦_⟧ : S.Carrier → T.Carrier
    ⟦_⟧⁻¹ : T.Carrier → S.Carrier
    cong : ∀ {x y} → x S.≈ y → ⟦ x ⟧ T.≈ ⟦ y ⟧
    cong⁻¹ : ∀ {x y} → x T.≈ y → ⟦ x ⟧⁻¹ S.≈ ⟦ y ⟧⁻¹
    linv : ∀ y → ⟦ ⟦ y ⟧⁻¹ ⟧ T.≈ y
    rinv : ∀ x → ⟦ ⟦ x ⟧ ⟧⁻¹ S.≈ x

IsoFlip : {S T : Setoid ℓ ℓ'} → Iso S T → Iso T S
IsoFlip f = record
  { ⟦_⟧ = ⟦_⟧⁻¹
  ; ⟦_⟧⁻¹ = ⟦_⟧
  ; cong = cong⁻¹
  ; cong⁻¹ = cong
  ; linv = rinv
  ; rinv = linv
  }
  where open Iso f

Hom≈ : ∀ {S T : Setoid ℓ ℓ'} (f g : Hom S T) → Prop (ℓ ⊔ ℓ')
Hom≈ {S = S} {T} f g = ∀ {x y} → x S.≈ y → f.⟦ x ⟧ T.≈ g.⟦ y ⟧
  where
  module S = Setoid S
  module T = Setoid T
  module f = Hom f
  module g = Hom g

_≅_ : ∀ {ℓ ℓ'} → Rel (Setoid ℓ ℓ') (ℓ ⊔ ℓ')
S ≅ T = ∥ Iso S T ∥

module _ {ℓ ℓ'} where
  isEquivalenceIso : IsEquivalence (_≅_ {ℓ} {ℓ'})
  isEquivalenceIso = record
    { refl = isReflexive
    ; sym = isSymmetric
    ; trans = isTransitive
    }
    where
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

  SetoidSetoid : Setoid (lsuc ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  SetoidSetoid = record
    { Carrier = Setoid ℓ ℓ'
    ; _≈_ = _≅_
    ; isEquivalence = isEquivalenceIso
    }
