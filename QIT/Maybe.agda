open import QIT.Prelude

module QIT.Maybe
  ⦃ pathElim* : PathElim ⦄
  where

data Maybe {ℓA} (A : Set ℓA) : Set ℓA where 
  nothing : Maybe A
  just : A → Maybe A

map : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → (A → B) → Maybe A → Maybe B
map f nothing = nothing
map f (just x) = just (f x)

return : ∀ {ℓA} {A : Set ℓA} (x : A) → Maybe A
return x = just x

_>>=_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → Maybe A → (A → Maybe B) → Maybe B
_>>=_ nothing _ = nothing
_>>=_ (just x) f = f x

_>>_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → Maybe A → Maybe B → Maybe B
_>>_ x y = x >>= λ _ → y

_<$>_ : ∀ {ℓA ℓB} {A : Set ℓA} {B : Set ℓB} → Maybe (A → B) → Maybe A → Maybe B
nothing <$> x = nothing
just f <$> nothing = nothing
just f <$> just x = just (f x)
