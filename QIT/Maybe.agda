open import QIT.Prelude
open import QIT.Prelude.Logic
open import QIT.Identity

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

join : ∀ {A : Set ℓA} → Maybe (Maybe A) -> Maybe A
join nothing          = nothing
join (just nothing)   = nothing
join (just (just x))  = just x

flatten : ∀ {A B : Set ℓA} → Maybe (A → Maybe B) → A → Maybe B
flatten f x = join (f <$> just x)

flatten1 : ∀ {A B : Set ℓA} → Maybe (A → Maybe B) → A → Maybe B
flatten1 f x = join (f <$> just x)

flatten2 : ∀ {A B C : Set ℓA} → (A → Maybe (B → Maybe C)) → A → B → Maybe C
flatten2 f x y = flatten (flatten (just f) x) y

flatten3 : ∀ {A B C D : Set ℓA}
  → (A → Maybe (B → Maybe (C → Maybe D)))
  → A → B → C → Maybe D
flatten3 f x y z = flatten (flatten (f x) y) z

just-inj : ∀ {ℓA} {A : Set ℓA} {x y : A}
  → just x ≡ just y → x ≡ y
just-inj refl = refl

just≢nothing : ∀ {X : Set} {x : X}
  → just x ≡ nothing → ⊥
just≢nothing ()
