module QIT.Examples.ConTy.DirectWeaklyTaggedEquiv where

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset

D→W : D.Initial → W.Initial
D→W (da , u) = w , {!!}
  where
  open ≡
  module DA = D.Algebra da
  data CT : Set where
    con : DA.Con → CT
    ty : (γ : DA.Con) → DA.Ty γ → CT
    k̂ : CT
    ĉ : CT
    t̂ : CT → CT
    # : CT
  [_] : CT → CT
  [ con a ] = ĉ
  [ ty γ a ] = t̂ (con γ)
  [ k̂ ] = k̂
  [ ĉ ] = k̂
  [ t̂ γ ] = k̂
  [ # ] = #
  ▷ : CT → CT → CT
  ▷ (con γ) (ty γ' a) = con (γ' DA.▷ a)
  ▷ (con x) _ = #
  ▷ _ _ = #
  k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
  k▷ (con γ) (ty γ' a) refl refl = refl

  w : W.Algebra
  w = record
    { CT = CT
    ; [_] = [_]
    ; k̂ = k̂
    ; kk̂ = refl
    ; ĉ = ĉ
    ; kĉ = refl
    ; t̂ = t̂
    ; kt̂ = λ _ _ → refl
    ; ∙ = con DA.∙
    ; k∙ = refl
    ; ▷ = ▷
    ; k▷ = {!!}
    ; u = {!!}
    ; ku = {!!}
    ; π = {!!}
    ; kπ = {!!}
    ; σ = {!!}
    ; kσ = {!!}
    ; σ▷ = {!!}
    ; σπ = {!!}
    }
