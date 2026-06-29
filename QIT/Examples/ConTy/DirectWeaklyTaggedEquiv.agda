open import QIT.Prelude

module QIT.Examples.ConTy.DirectWeaklyTaggedEquiv ⦃ a!c* : A!C ⦄ where

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset

D→W : D.Initial → W.Initial
D→W (da , iu) = w , {!!}
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

  con-inj : ∀ {γ δ} → con γ ≡ con δ → γ ≡ δ
  con-inj refl = refl

  ty-inj₁ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ} → ty γ a ≡ ty δ b → γ ≡ δ
  ty-inj₁ refl = refl

  ty-inj₂ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ}
    → (p : ty γ a ≡ ty δ b) → subst DA.Ty (ty-inj₁ p) a ≡ b
  ty-inj₂ refl = refl

  t̂-inj : ∀ {γ δ} → t̂ γ ≡ t̂ δ → γ ≡ δ
  t̂-inj refl = refl

  t̂-γ : (γ a : CT) → [ a ] ≡ t̂ γ → [ γ ] ≡ ĉ
  t̂-γ (con _) _ _ = refl
  t̂-γ (ty _ _) (ty _ _) ()
  t̂-γ k̂ (ty _ _) ()
  t̂-γ ĉ (ty _ _) ()
  t̂-γ (t̂ _) (ty _ _) ()
  t̂-γ # (ty _ _) ()

  ▷ : CT → CT → CT
  ▷ (con γ) (ty γ' a) = con (γ' DA.▷ a)
  ▷ (con x) _ = #
  ▷ _ _ = #
  k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
  k▷ (con γ) (ty γ' a) refl refl = refl

  k▷-a : {!!}

  u : CT → CT
  u (con γ) = ty γ (DA.u γ)
  u _ = #

  ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
  ku (con γ) refl = refl

  π : CT → CT → CT → CT
  π (con γ) (ty γ' a) (ty δ b) = ty γ' (DA.π a {!!})
  π (con γ) (ty γ' a) _ = {!!}
  π (con γ) _ b = {!!}
  π _ _ _ = #

  open import Data.Maybe
  gt : CT → Maybe DA.Con
  gt (con γ) = nothing
  gt (ty γ a) = just γ
  gt k̂ = nothing
  gt ĉ = nothing
  gt (t̂ γ) = nothing
  gt # = nothing

  ĉ→Con : (γ : CT) → [ γ ] ≡ ĉ → DA.Con
  ĉ→Con (con γ) _ = γ

  v : (γ a : CT)
    → (p : [ γ ] ≡ ĉ) → [ a ] ≡ t̂ γ
    → [ ▷ γ a ] ≡ ĉ
    → gt a ≡ just (ĉ→Con γ p)
  v (con γ) (ty γ' a) refl q refl = cong just (con-inj (t̂-inj q))

  kπ-a : (γ a b : CT) →
          [ γ ] ≡ ĉ → [ b ] ≡ t̂ (▷ γ a) → [ π γ a b ] ≡ t̂ γ → [ a ] ≡ t̂ γ
  kπ-a (con γ) (con x) b p q r = {!!}
  kπ-a (con γ) (ty γ₁ a) b p q r = {!!}
  kπ-a (con γ) k̂ b p q r = {!!}
  kπ-a (con γ) ĉ b p q r = {!!}
  kπ-a (con γ) (t̂ a) b p q r = {!!}
  kπ-a (con γ) # b p q r = {!!}
  kπ-b : {!!}
  kπ :   {!!}
  σ :    {!!}
  kσ-a : {!!}
  kσ-b : {!!}
  kσ :   {!!}
  σ▷ :   {!!}
  σπ :   {!!}


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
    ; t̂-γ = t̂-γ
    ; ∙ = con DA.∙
    ; k∙ = refl
    ; ▷ = ▷
    ; k▷ = k▷
    ; k▷-a = {!!}
    ; u =    u 
    ; ku =   ku
    ; π =    π
    ; kπ-a = kπ-a
    ; kπ-b = kπ-b
    ; kπ =   kπ
    ; σ =    σ
    ; kσ-a = kσ-a
    ; kσ-b = kσ-b
    ; kσ =   kσ
    ; σ▷ =   σ▷
    ; σπ =   σπ
    }
