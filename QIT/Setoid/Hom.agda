module QIT.Setoid.Hom where

open import QIT.Prelude
open import QIT.Setoid.Base
open import Data.Product

record Hom {ℓS ℓS' ℓT ℓT'}
       (S : Setoid ℓS ℓS') (T : Setoid ℓT ℓT') : Set (ℓS ⊔ ℓS' ⊔ ℓT ⊔ ℓT')
       where
  module S = Setoid S
  module T = Setoid T
  field
    to : S.Carrier → T.Carrier
    cong : ∀ {x y} → x S.≈ y → to x T.≈ to y

idHom : ∀ {ℓ ℓ'} → {S : Setoid ℓ ℓ'} → Hom S S
idHom {S} = record
  { to = λ x → x
  ; cong = λ p → p }

_≈h_ : ∀ {ℓS ℓS' ℓT ℓT'} → {S : Setoid ℓS ℓS'} {T : Setoid ℓT ℓT'}
     → (f g : Hom S T) → Prop (ℓS ⊔ ℓS' ⊔ ℓT')
_≈h_ {S = S} {T} f g = ∀ {x y} → x S.≈ y → f.to x T.≈ g.to y
  where
  module S = Setoid S
  module T = Setoid T
  module f = Hom f
  module g = Hom g

infixr 1 _∘_
_∘_ : ∀ {ℓA ℓA' ℓB ℓB' ℓC ℓC' }
    → {A : Setoid ℓA ℓA'} {B : Setoid ℓB ℓB'} {C : Setoid ℓC ℓC'}
    → Hom B C → Hom A B → Hom A C
f ∘ g = record
  { to  = λ x → f.to (g.to x)
  ; cong = λ x≈y → f.cong (g.cong x≈y)
  }
  where
  module f = Hom f
  module g = Hom g
