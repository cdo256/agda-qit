module Mobile where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Function.Bijection hiding (_∘_)
open import Relation.Binary.PropositionalEquality as ≡
open import Axiom
open import Setoid as S

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

data BTree (B : Set ℓ) : Set ℓ where
  leaf : BTree B
  node : (f : B → BTree B) → BTree B

module Mobile (B : Set ℓ) where
  Bˢ : S.Setoid ℓ ℓ
  Bˢ = {!!}
  open Bijection
  data _≈ᵗ_ : BTree B → BTree B → Set where
    ≈leaf : leaf ≈ᵗ leaf
    ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
          → node f ≈ᵗ node g
    ≈perm : ∀ {f} → (π : Bijection Bˢ Bˢ)
          → node f ≈ᵗ node λ b → f ({!π .to b!})
    ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

  ≈refl : ∀ {t} → t ≈ᵗ t
  ≈refl {leaf} = ≈leaf
  ≈refl {node f} = ≈node λ b → ≈refl {f b}

  ≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
  ≈sym (≈perm {f} π) =
    subst
      (λ h → node (f ∘ π .to) ≈ node (f ∘ h))
      (funExt {!rightInv π!})
      (≈perm {f = f ∘ π .to} {!invIso π!})
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  -- MobileSetoid : Setoid ℓ-zero ℓ-zero
  -- MobileSetoid = BTree B , record
  --   { _≈_ = _≈ᵗ_
  --   ; equiv = equivRel
  --     (λ t → ≈refl {t})
  --     (λ _ _ p → ≈sym p)
  --     (λ _ _ _ p q → ≈trans p q) }
