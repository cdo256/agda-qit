open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base
open import Data.Bool
open import QIT.Relation.Subset
open import QIT.Relation.Nullary

V : Set₁
V = W Set λ X → X

∅ : V
∅ = sup (⊥ , λ ())

𝟙 : V
𝟙 = sup (⊤ , λ {tt → sup (⊥ , λ ())})

-- 𝒫 : V → V
-- 𝒫 (sup (A , _∈A)) = sup (A , λ b → {!b ∈A!})

⟨_⟩ : V → Set
⟨ sup (X , f) ⟩ = X

_∈_ : V → V → Prop₁
y ∈ sup (X , f) = ∃ λ x → f x ≡ y

comp : V → (V → Prop) → V
comp (sup (X , fX)) ϕ = sup (X' , λ z → fX (z .fst))
  where
  X' = ΣP X λ z → ϕ (fX z)

comp' : V → (V → Bool) → V
comp' X ϕ = comp X λ x → True (ϕ x)

𝒫 : V → V
𝒫 (sup (X , fX)) = sup ((X → Bool) , λ ϕ → comp' (sup (X , fX)) {!!})
  where
  PX : Set
  PX = ΣP (X → Bool) λ ϕ → {!comp'!}

-- -- 𝒫 : V → V
-- -- 𝒫 (sup (A , f)) = sup ({!A → V!} , {!!})

-- -- [_,_] : V → V → V
-- -- [ sup (A , f) , sup (B , g) ] =
-- --   sup ((A × B) , λ (x , y) → {!!})

-- -- -- _∈_ : V → V → Prop
-- -- -- sup (x , g) ∈ sup (A , f) = {!!}
