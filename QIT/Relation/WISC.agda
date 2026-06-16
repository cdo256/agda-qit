module QIT.Relation.WISC where

open import QIT.Prelude
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Ordinal
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Set.Base
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Functor.Base

Family : ∀ ℓ ℓ' → Set (lsuc ℓ ⊔ lsuc ℓ')
Family ℓ ℓ' = Σ (Set ℓ) λ I → I → Set ℓ'

OrdFamily : ∀ ℓI ℓX ℓ< → Set (lsuc ℓI ⊔ lsuc ℓX ⊔ lsuc ℓ<)
OrdFamily ℓI ℓX ℓ< = Σ (Set ℓI) λ I → Σ (I → Set ℓX) λ X → ∀ i → IsOrdinal ℓ< (X i)

-- Cover : ∀ {ℓY} (Y : Set ℓY) → ∀ ℓI ℓX → Set (ℓY ⊔ lsuc ℓI ⊔ lsuc ℓX)  
-- Cover Y ℓI ℓX =
--   Σ (Family ℓI ℓX)
--   λ (I , X) → (i : I) → X i ↠ Y
-- 
-- OrdCover : ∀ {ℓY} (Y : Set ℓY) → ∀ ℓI ℓX ℓ< → Set (ℓY ⊔ lsuc ℓI ⊔ lsuc ℓX ⊔ lsuc ℓ<)
-- OrdCover Y ℓI ℓX ℓ< =
--   Σ (OrdFamily ℓI ℓX ℓ<)
--   λ (I , X , _) → (i : I) → X i ↠ Y

-- record Cover {ℓY} (Y : Set ℓY) (ℓA : Level) : Set (ℓY ⊔ lsuc ℓA) where
--   field
--     A : Set ℓA
--     p : A → Y
--     surj : Surjective p

record Cover {ℓY} (Y : Set ℓY) (ℓA ℓX : Level) : Set (ℓY ⊔ lsuc ℓX ⊔ lsuc ℓA) where
  field
    A : Y → Set ℓA
    inhabA : ∀ {y} → ∥ A y ∥ 
    X : ∀ {y} → A y → Set ℓX

record OrdCover {ℓY} (Y : Set ℓY) (ℓA ℓα ℓ< : Level)
  : Set (lsuc ℓY ⊔ lsuc ℓα ⊔ lsuc ℓ< ⊔ lsuc ℓA) where
  field
    A : Y → Set ℓA
    inhabA : ∀ {y} → ∥ A y ∥
    α : ∀ {y} → A y → Set ℓα
    isOrd-α : ∀ {y} (a : A y) → IsOrdinal ℓ< (α a)

record IsCoverFamWeaklyInitial {ℓI ℓY ℓA ℓX} (Y : Set ℓY)
  : Set (lsuc ℓY ⊔ lsuc ℓX ⊔ lsuc ℓA ⊔ lsuc ℓI) where
  open Cover
  field
    I : Set ℓI
    cover : I → Cover Y ℓA ℓX
    univ : ∀ (𝓑 : Cover Y ℓA ℓX)
         → ∃ λ i → ∥ (∀ y → cover i .A y → 𝓑 .A y) ∥

record IsOrdCoverFamWeaklyInitial {ℓI ℓY ℓA ℓα ℓ<} (Y : Set ℓY)
  : Set (lsuc ℓY ⊔ lsuc ℓα ⊔ lsuc ℓ< ⊔ lsuc ℓA ⊔ lsuc ℓI) where
  open OrdCover
  field
    I : Set ℓI
    cover : I → OrdCover Y ℓA ℓα ℓ<
    univ : ∀ (𝓑 : OrdCover Y ℓA ℓα ℓ<)
         → ∃ λ i → ∥ (∀ y → cover i .A y → 𝓑 .A y) ∥


WISC : ∀ {ℓY} ℓI ℓA ℓB → (Y : Set ℓY)
     → Set (ℓY ⊔ lsuc ℓI ⊔ lsuc ℓA ⊔ lsuc ℓB)
WISC ℓI ℓA ℓB Y = ΣP {!CoverFamily Y !} {!!}

-- OWISC : ∀ {ℓY} ℓI ℓA ℓB ℓα ℓ< → (Y : Set ℓY)
--       → Set (ℓY ⊔ lsuc ℓI ⊔ lsuc ℓA ⊔ lsuc ℓB ⊔ lsuc ℓα ⊔ lsuc ℓ<)
-- OWISC {ℓY} ℓI ℓA ℓB ℓα ℓ< Y = ΣP (OrdCoverFamily Y ℓI ℓA ℓα ℓ<) (IsOWISCFamily ℓB Y)
