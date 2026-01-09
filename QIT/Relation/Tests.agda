module QIT.Relation.Tests where

module Test1 where
  open import QIT.Prelude
  open import Data.Nat as ℕ hiding (_≤_; _<_)

  open import QIT.Container.Base
  data S : Set where
    zero : S
    suc : S
    lim : S

  P : S → Set
  P zero = ⊥
  P suc = ⊤
  P lim = ℕ

  T = W S P
  open import QIT.Relation.Plump S P

  [_] : ℕ → T
  [ zero ] = sup (zero , λ())
  [ suc n ] = sup (suc , λ _ → [ n ])

  ω : T
  ω = sup (lim , λ n → [ n ])

  ω' : T
  ω' = sup (lim , λ n → [ suc n ])

  _≤'_ : T → T → Prop
  s ≤' t = ιᶻ s ≤ ιᶻ t
  _<'_ : T → T → Prop
  s <' t = ιᶻ s < ιᶻ t

  0≤t : ∀ t → sup (zero , λ()) ≤' t
  0≤t t = sup≤ λ()

  t<suc : ∀ t → t <' sup (suc , λ _ → t)
  t<suc t = <sup tt (≤refl (ιᶻ t))

  ω≤ω' : ιᶻ ω ≤ ιᶻ ω'
  ω≤ω' = sup≤ (λ n → <sup n (<→≤ (t<suc [ n ])))

  ω'≤ω : ιᶻ ω' ≤ ιᶻ ω
  ω'≤ω = sup≤ (λ n → <sup (suc n) (≤refl _))
