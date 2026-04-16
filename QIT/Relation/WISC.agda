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

record Cover {ℓY} (Y : Set ℓY) (ℓA : Level) : Set (ℓY ⊔ lsuc ℓA) where
  field
    A : Set ℓA
    p : A → Y
    surj : Surjective p

record OrdKCover {ℓY} (Y : Set ℓY) (ℓA ℓα ℓ< : Level) : Set (ℓY ⊔ lsuc ℓA ⊔ lsuc ℓα ⊔ lsuc ℓ<) where
  field
    A : Set ℓA
    p : A → Y
    surj : Surjective p
    α : A → Set ℓα
    isOrd-α : (a : A) → IsOrdinal ℓ< (α a)

CoverFamily : ∀ {ℓY} (Y : Set ℓY) → ∀ ℓI ℓA → Set _
CoverFamily Y ℓI ℓA =
  Σ (Set ℓI) λ I → I → Cover Y ℓA

OrdCoverFamily : ∀ {ℓY} (Y : Set ℓY) → ∀ ℓI ℓA ℓO ℓ< → Set _
OrdCoverFamily Y ℓI ℓA ℓO ℓ< =
  Σ (Set ℓI) λ I → I → OrdKCover Y ℓA ℓO ℓ<

IsWISCFamily :
  ∀ {ℓY ℓI ℓA} ℓB → (Y : Set ℓY) →
  CoverFamily Y ℓI ℓA → Prop (ℓY ⊔ ℓI ⊔ ℓA ⊔ lsuc ℓB)
IsWISCFamily ℓB Y (I , C) =
  ∀ (B : Cover Y ℓB) →
  ∃ λ (i : I) → ∃ λ (f : C i .A → B .A) →
  ∀ x → C i .p x ≡ B .p (f x)
  where
  open Cover

-- IsOWISCFamily :
--   ∀ {ℓY ℓI ℓA ℓO ℓ<} ℓB → (Y : Set ℓY) →
--   OrdCoverFamily Y ℓI ℓA ℓO ℓ< → Prop (ℓY ⊔ ℓI ⊔ ℓA ⊔ lsuc ℓB ⊔ lsuc ℓO ⊔ lsuc ℓ<)
-- IsOWISCFamily {ℓO = ℓO} {ℓ< = ℓ<} ℓB Y (I , C) =
--   (B : OrdKCover Y ℓB ℓO ℓ<) →
--   ∃' λ i → ((y : Y) → C i .A y → B .A y)
--   where open OrdKCover

-- WISC : ∀ {ℓY} ℓI ℓA ℓB ℓα → (Y : Set ℓY)
--      → Set (ℓY ⊔ lsuc ℓI ⊔ lsuc ℓA ⊔ lsuc ℓB ⊔ lsuc ℓα)
-- WISC ℓI ℓA ℓB ℓα Y = ΣP (CoverFamily Y ℓI ℓA ℓα) (IsWISCFamily ℓB ℓα Y)

-- OWISC : ∀ {ℓY} ℓI ℓA ℓB ℓα ℓ< → (Y : Set ℓY)
--       → Set (ℓY ⊔ lsuc ℓI ⊔ lsuc ℓA ⊔ lsuc ℓB ⊔ lsuc ℓα ⊔ lsuc ℓ<)
-- OWISC {ℓY} ℓI ℓA ℓB ℓα ℓ< Y = ΣP (OrdCoverFamily Y ℓI ℓA ℓα ℓ<) (IsOWISCFamily ℓB Y)
