open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.SetQuotient

module QIT.Setoid.IndexedQuotient
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  where

open import QIT.Relation.Base
open import QIT.Relation.IndexedBinary
import QIT.Setoid.Indexed as IS
open import QIT.Setoid.Base as S
open import QIT.Setoid.Quotient

_/≈ᴵ : {I : Set ℓI} → IS.Setoid ℓA ℓR I → Set (ℓI ⊔ ℓA ⊔ ℓR)
S /≈ᴵ = IS.IndexedSetoid→UnindexedSetoid S /≈

-- lemma : ∀ {ℓA ℓR ℓB ℓS}
--     → (Ã : Setoid ℓA ℓR)
--     → (B̃ : IS.Setoid ℓB ℓS (Ã /≈))
--     → (f₀ : (x : ⟨ Ã ⟩) → IS.⟨ B̃ ⟩ (Ã ⊢[ x ]))
--     → (f-cong : ∀ {x y : ⟨ Ã ⟩} → (p : Ã [ x ≈ y ])
--               → B̃ IS.[ f₀ x ≈ f₀ y ])
--     → ∀ {x y} → (p : Ã [ x ≈ y ])
--     → subst ? (Ã ⊢≈[ p ]) (f x) ≡ f y  

dmap : ∀ {ℓA ℓR ℓB ℓS}
    → (Ã : Setoid ℓA ℓR)
    → (B̃ : IS.Setoid ℓB ℓS (Ã /≈))
    → (f₀ : (x : ⟨ Ã ⟩) → IS.⟨ B̃ ⟩ (Ã ⊢[ x ]))
    → (f-cong : ∀ {x y : ⟨ Ã ⟩} → (p : Ã [ x ≈ y ]) → B̃ IS.[ f₀ x ≈ f₀ y ])
    → (x : Ã /≈) → IS.FiberSetoid B̃ x /≈
dmap Ã B̃ f₀ f-cong =
  SQ.elim Ã F̃/ dmap₀ dmap-cong
  where
  F̃ : Ã /≈ → Setoid _ _
  F̃ x = IS.FiberSetoid B̃ x
  F̃/ : Ã /≈ → Set _
  F̃/ x = F̃ x /≈
  B̃x : (x : ⟨ Ã ⟩) → Setoid _ _
  B̃x x = F̃ (Ã ⊢[ x ])
  B̃x/ : (x : ⟨ Ã ⟩) → Set _
  B̃x/ x = F̃/ (Ã ⊢[ x ])
  ΣB : Setoid _ _
  ΣB = IS.IndexedSetoid→UnindexedSetoid B̃
  dmap₀ : ∀ x → B̃x/ x
  dmap₀ x = B̃x x ⊢[ f₀ x ]
  dmap-cong : ∀ {x y} → (p : Ã [ x ≈ y ])
    → subst F̃/ (Ã ⊢≈[ p ]) (dmap₀ x) ≡ dmap₀ y  
  dmap-cong {x} {y} p =
    let u : ΣB ⊢[ Ã ⊢[ x ] , f₀ x ] ≡ ΣB ⊢[ Ã ⊢[ y ] , f₀ y ]
        u = ΣB ⊢≈[ f-cong p ] in {!!}
    where open ≡.≡-Reasoning
--   SQ.elim Ã (λ x → B̃ ⊢[ f₀ x ])
--            (λ p → B̃ ⊢≈[ f-cong p ])
--   where
--   module B = Setoid B̃
