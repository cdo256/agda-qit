module Mobile where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.Bundles
open import Function.Bundles
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Data.Product.Function.Dependent.Setoid 
open import Relation.Binary.Morphism.Bundles 
open import Setoid as S
open import Data.Product

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

data BTree (B : Set ℓ) : Set ℓ where
  leaf : BTree B
  node : (f : B → BTree B) → BTree B
    
module BOrdinal (B : Set) where
  data Ord : Set where
    zero : Ord
    suc : Ord → Ord
    lim : (B → Ord) → Ord

  data _<_ : Ord → Ord → Set where
    <suc : ∀ α → α < suc α
    <lim : ∀ α f i → α < f i → α < lim f
    <trans : ∀ {s t u} → s < t → t < u → s < u

  _≤_ : Ord → Ord → Set
  s ≤ t = ∀ u → (p : u < s) → u < t

  data _≈_ : Ord → Ord → Set where
    ≈ext : ∀ {s t} → (le : s ≤ t) (ge : t ≤ s)
         → s ≈ t

  ⊂_ : Ord → Set
  ⊂ α = Σ[ β ∈ Ord ] β < α

  infixl 30  _+_ 
  _+_ : Ord → Ord → Ord
  α + zero = α
  α + suc β = suc (α + β)
  α + lim f = lim (λ i → α + f i)

-- module ωOrdinal where
--   open BOrdinal ℕ public
--   ℕ→Ord : ℕ → Ord 
--   ℕ→Ord zero = zero
--   ℕ→Ord (suc ω) = suc (ℕ→Ord ω)
--   ω : Ord
--   ω = lim ℕ→Ord
--   0<ω : zero < ω
--   0<ω = <lim zero ℕ→Ord 1 (<suc zero)
    

-- module BoundedOrdinal (Γ : ωOrdinal.Ord) where
--   module Γ = ωOrdinal
--   open Γ using (⊂_; _+_)
--   data Ord : Set where
--     zero : Ord
--     suc : Ord → Ord
--     lim : (ℕ → Ord) → Ord

--   data lt : (φ : ⊂ Γ) → Ord → Ord → Set where
--     <suc : ∀ φ β → lt φ β (suc β)
--     <lim : ∀ φ β {φ<Γ} f i → (p : Γ.suc φ Γ.< Γ) → lt (φ , φ<Γ) β (f i)
--          → lt (Γ.suc φ , p) β (lim f)
--     <trans : ∀ φ φ' {φ<Γ φ'<Γ} {s t u}
--            → (p : φ + φ' Γ.< Γ)
--            → lt (φ , φ<Γ) s t
--            → lt (φ' , φ'<Γ) t u
--            → lt (φ + φ' , p) s u

--   _<_ : Ord → Ord → Set
--   β < γ = Σ[ φ ∈ ⊂ Γ ] lt φ β γ

--   _≤_ : Ord → Ord → Set
--   s ≤ t = ∀ u → (p : u < s) → u < t

--   data _≈_ : Ord → Ord → Set where
--     ≈ext : ∀ {s t} → (le : s ≤ t) (ge : t ≤ s)
--          → s ≈ t

--   ≈refl : ∀ {t} → t ≈ t
--   ≈refl {t} = ≈ext (λ _ p → p) (λ _ p → p)
 
--   ≈sym : ∀ {s t} → s ≈ t → t ≈ s
--   ≈sym (≈ext le ge) = ≈ext ge le
 
--   ≈trans : ∀ {s t u} → s ≈ t → t ≈ u → s ≈ u
--   ≈trans (≈ext s≤t s≥t) (≈ext t≤u u≥t) =
--     ≈ext (λ _ p → t≤u _ (s≤t _ p)) λ _ p → s≥t _ (u≥t _ p)

--   OrdinalSetoid : Setoid ℓ-zero ℓ-zero
--   OrdinalSetoid = Ord , record
--     { _≈_ = _≈_
--     ; equiv = equivRel
--       (λ t → ≈refl {t})
--       (λ _ _ p → ≈sym p)
--       (λ _ _ _ p q → ≈trans p q) }

--   ℕ→Ord : ℕ → Ord
--   ℕ→Ord zero = zero
--   ℕ→Ord (suc ω) = suc (ℕ→Ord ω)
--   ω : Ord
--   ω = lim ℕ→Ord
--   0<ω : zero < ω
--   0<ω = {!!} , (<lim Γ.zero zero ℕ→Ord 1 {!!} (<suc (Γ.zero , {!!}) zero))

--   -- data isChild : (α β : Ord) → Set ℓ-zero where
--   --   ischild : ∀ f i → isChild (node f) (f i) 
  
--   -- -- not decidable.
--   -- -- isChild? : (α β : Ord) → Dec (isChild α β)

--   -- -- Not definable in general since we need arbitrary branching.
--   -- -- lim' : (f : Ord → Ord) → Ord 

--   -- infixl 30  _+ᵒ_ 
--   -- _+ᵒ_ : Ord → Ord → Ord
--   -- α +ᵒ 𝟘 = α
--   -- α +ᵒ lim f = lim λ i → α +ᵒ f i

--   -- _ : (ℕ→Ord 1) +ᵒ (ℕ→Ord 1) ≈ (ℕ→Ord 2)
--   -- _ = ≈ext le ge
--   --   where
--   --   le : (ℕ→Ord 1 +ᵒ ℕ→Ord 1) ≤ ℕ→Ord 2
--   --   le 𝟘 p = p
--   --   le (lim f) p = p
--   --   ge : ℕ→Ord 2 ≤ (ℕ→Ord 1 +ᵒ ℕ→Ord 1)
--   --   ge = λ u p → p

--   -- -- Probably not decidable
--   -- -- 1+ω≈ω : 𝟙 +ᵒ ω ≈ ω

--   -- -- Does this bring in an extra successor?
--   -- _∙ᵒ_ : Ord → Ord → Ord
--   -- α ∙ᵒ 𝟘 = 𝟘
--   -- α ∙ᵒ lim f = lim (λ i → α ∙ᵒ f i)

--   iterOrd : {A : Set} → Ord → A → (A → A) → ((ℕ → A) → A) → A 
--   iterOrd zero z s l = z
--   iterOrd (suc α) z s l = s (iterOrd α z s l)
--   iterOrd (lim π) z s l = l (λ i → iterOrd (π i) z s l)

-- module Mobile (B : Set) where
--   open Iso
--   data _≈_ : BTree B → BTree B → Set where
--     ≈leaf : leaf ≈ leaf
--     ≈node : ∀ {f g} → (c : ∀ b → f b ≈ g b)
--           → node f ≈ node g
--     ≈perm : ∀ {f} → (π : Iso B B)
--           → node f ≈ node (f ∘ π .fun)
--     ≈trans : ∀ {s t u} → s ≈ t → t ≈ u → s ≈ u

--   ≈refl : ∀ {t} → t ≈ t
--   ≈refl {leaf} = ≈leaf
--   ≈refl {node f} = ≈node λ b → ≈refl {f b}

--   ≈sym : ∀ {s t} → s ≈ t → t ≈ s
--   ≈sym ≈leaf = ≈leaf
--   ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
--   ≈sym (≈perm {f} π) =
--     subst
--       (λ h → node (f ∘ fun π) ≈ node (f ∘ h))
--       (funExt (rightInv π))
--       (≈perm {f = f ∘ fun π} (invIso π))
--   ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

--   MobileSetoid : Setoid ℓ-zero ℓ-zero
--   MobileSetoid = BTree B , record
--     { _≈_ = _≈_
--     ; equiv = equivRel
--       (λ t → ≈refl {t})
--       (λ _ _ p → ≈sym p)
--       (λ _ _ _ p q → ≈trans p q) }
