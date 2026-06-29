open import QIT.Prelude

module QIT.IIT.Cont1 ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Nat
open import QIT.Fin.Base

module _ where
  data SortSig : Set
  data Sort : SortSig → Set
  data SortVar : SortSig → Set

  infixl 20 _▷_
  data SortSig where
    ∙ : SortSig
    _▷_ : (Γ : SortSig) → Sort Γ → SortSig

  data Sort where
    U : ∀ {Γ} → Sort Γ
    V : ∀ {Γ} → SortVar Γ → Sort Γ
    Π̂ : ∀ {Γ} → (A : SortVar Γ)
      → (B : Sort (Γ ▷ V A))
      → Sort Γ

  data SortVar where
    vz : ∀ {Γ A} → SortVar (Γ ▷ A)
    vs : ∀ {Γ A} → SortVar Γ → SortVar (Γ ▷ A)

-- examples: ℕ and ConTy
module _ where
  N : SortSig
  N = ∙ ▷ U

  ConTy : SortSig
  ConTy = ∙ ▷ U ▷ V vz ▷ Π̂ (vs vz) U 

module _ where
  data SP : SortSig → Set where
    cv : ∀ {Γ} → SortVar Γ → SP Γ
    Πᶜ : ∀ {Γ} → SP Γ → SP Γ
