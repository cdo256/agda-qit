module QIT.Examples.WFTree (S : Set) (P : S → Set) where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Subset
open import QIT.Relation.Binary
open import QIT.Relation.WellFounded
open import QIT.Container.Base

record WFTree : Set₁ where
  field
    A : Set
    ∙ : A
    ↑ : A → A
    _≺_ : A → A → Prop -- is parent of

  _≪_ : A → A → Prop
  x ≪ y = (x ≡p y) ∨ x ≺ y

  field
    ≺step : ∀ x y → x ≺ y → x ≪ ↑ y
    ↑≺ : ∀ x → x ≡.≢ ∙ → ↑ x ≺ x
    trans : Transitive _≺_

T = W S P

data Path : Set where
  base : Path
  step : (s : S) (f : P s → T) (i : P s) → Path

Path→T : T → Path → T
Path→T t base = t
Path→T t (step s f i) = sup (s , f)

module _ (t : S) (g : P t → T) where
  α : T
  α = sup (t , g)
  -- A = Σ (W S P) (α ≤_)
  -- ↑ : A → A
  -- ↑ (β , sup≤ g<β) = {!!}
  -- W→WFTree : WFTree
  -- W→WFTree = record
  --   { A = A
  --   ; ∙ = sup (t , g) , {!!}
  --   ; ↑ = {!!}
  --   ; _≺_ = {!!}
  --   ; ≺step = {!!}
  --   ; ↑≺ = {!!}
  --   ; trans = {!!}
  --   }
