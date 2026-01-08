open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.QW.Equation using (Equation)
open import QIT.QW.Signature

module QIT.QW.Algebra {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
  open Sig sig
  open import QIT.Container.Functor S P
  open import QIT.QW.Equation S P

  private
    F̂ = F (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)

  record Alg : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ ℓV) where
    field
      alg : ≈.Algebra F̂
      sat : Sat alg Ξ

  record Hom (Xα Yβ : Alg) : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ ℓV) where
    field
      hom : ≈.Alg.Hom F̂ (Alg.alg Xα) (Alg.alg Yβ)

    open ≈.Alg.Hom hom renaming (hom to alghom) public

  record IsInitial (Xα : Alg) : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ ℓV) where
    open Hom
    field
      rec : ∀ Yβ → Hom Xα Yβ
      unique : ∀ Yβ (f : Hom Xα Yβ) → f .alghom ≈h (rec Yβ) .alghom

  record Record : Set (lsuc ℓS ⊔ lsuc ℓP ⊔ ℓE ⊔ ℓV) where
    field
      Xα : Alg
      initial : IsInitial Xα
