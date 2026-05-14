module QIT.Examples.ConTy.QW where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary

data S : Set where
  s[] : S
  sk̂ : S
  sĉ : S
  st̂ : S
  s∙ : S
  s▷ : S
  su : S
  sπ : S
  sσ : S

data P : S → Set where
  p[] : P s[]
  pt̂ : P st̂
  p▷-γ : P s▷
  p▷-a : P s▷
  pu-γ : P su
  pπ-γ : P sπ
  pπ-a : P sπ
  pπ-b : P sπ
  pσ-γ : P sσ
  pσ-a : P sσ
  pσ-b : P sσ

open import QIT.QW.Signature
open import QIT.QW.W
open import QIT.Container.Base
open import QIT.QW.Equation S P ℓ0

module Equations where
  data E : Set where
    ekk̂ : E
    ekĉ : E
    ekt̂ : E
    ek∙ : E
    ek▷ : E
    eku : E
    ekπ : E
    ekσ : E
    eσ▷ : E
    eσπ : E

  data V : Set where
    vγ : V
    va : V
    vb : V
    vc : V

  data B : E → Set where
    bkt̂-kγ : B ekt̂
    bk▷-kγ : B ek▷
    bk▷-ka : B ek▷
    bk▷-kb : B ek▷
    bku-kγ : B eku
    bkπ-kγ : B ekπ
    bkπ-ka : B ekπ
    bkπ-kb : B ekπ
    bkσ-kγ : B ekσ
    bkσ-ka : B ekσ
    bkσ-kb : B ekσ
    bσ▷-kγ : B eσ▷
    bσ▷-ka : B eσ▷
    bσ▷-kb : B eσ▷
    bσ▷-kc : B eσ▷
    bσπ-kγ : B eσπ
    bσπ-ka : B eσπ
    bσπ-kb : B eσπ
    bσπ-kc : B eσπ


  [_] : Expr V → Expr V
  [ x ] = supᴱ s[] (λ _ → x)

  k̂ : Expr V
  k̂ = supᴱ sk̂ λ ()
  ĉ : Expr V
  ĉ = supᴱ sĉ λ ()
  t̂ : Expr V → Expr V
  t̂ γ = supᴱ st̂ f
    where
    f : P st̂ → Expr V
    f pt̂-γ = γ

  ∙ : Expr V
  ∙ = supᴱ s∙ λ ()
  ▷ : Expr V → Expr V → Expr V
  ▷ γ a = supᴱ s▷ f
    where
    f : P s▷ → Expr V
    f p▷-γ = γ
    f p▷-a = a
  u : Expr V → Expr V
  u γ = supᴱ su f
    where
    f : P su → Expr V
    f pu-γ = γ
  π : Expr V → Expr V → Expr V → Expr V
  π γ a b = supᴱ sπ f
    where
    f : P sπ → Expr V
    f pπ-γ = γ
    f pπ-a = a
    f pπ-b = b
  σ : Expr V → Expr V → Expr V → Expr V
  σ γ a b = supᴱ sσ f
    where
    f : P sσ → Expr V
    f pσ-γ = γ
    f pσ-a = a
    f pσ-b = b

  v : V → Expr V
  v v = varᴱ v {λ()}

  γ = v vγ
  a = v va
  b = v vb
  c = v vc

  PE : ∀ e → B e → Expr V × Expr V
  PE ekt̂ bkt̂-kγ = [ γ ] , ĉ
  PE ek▷ bk▷-kγ = [ γ ] , ĉ
  PE ek▷ bk▷-ka = [ a ] , t̂ γ
  PE ek▷ bk▷-kb = [ b ] , t̂ (▷ γ a)
  PE eku bku-kγ = [ γ ] , ĉ
  PE ekπ bkπ-kγ = [ γ ] , ĉ
  PE ekπ bkπ-ka = [ a ] , t̂ γ
  PE ekπ bkπ-kb = [ b ] , t̂ (▷ γ a)
  PE ekσ bkσ-kγ = [ γ ] , ĉ
  PE ekσ bkσ-ka = [ a ] , t̂ γ
  PE ekσ bkσ-kb = [ b ] , t̂ (▷ γ a)
  PE eσ▷ bσ▷-kγ = [ γ ] , ĉ
  PE eσ▷ bσ▷-ka = [ a ] , t̂ γ
  PE eσ▷ bσ▷-kb = [ b ] , t̂ (▷ γ a)
  PE eσ▷ bσ▷-kc = [ c ] , t̂ (▷ (▷ γ a) b)
  PE eσπ bσπ-kγ = [ γ ] , ĉ
  PE eσπ bσπ-ka = [ a ] , t̂ γ
  PE eσπ bσπ-kb = [ b ] , t̂ (▷ γ a)
  PE eσπ bσπ-kc = [ c ] , t̂ (▷ (▷ γ a) b)

  PC : E → Expr V × Expr V
  PC ekk̂ = [ k̂ ] , k̂
  PC ekĉ = [ ĉ ] , k̂
  PC ekt̂ = [ t̂ γ ] , k̂
  PC ek∙ = [ ∙ ] , ĉ
  PC ek▷ = [ ▷ γ a ] , ĉ
  PC eku = [ u γ ] , t̂ γ
  PC ekπ = [ π γ a b ] , t̂ γ
  PC ekσ = [ σ γ a b ] , t̂ γ
  PC eσ▷ = ▷ (σ γ a b) c , ▷ (▷ (▷ γ a) b) c
  PC eσπ = π γ a (π (▷ γ a) b c) , π γ (σ γ a b) c

  Ξ : E → EquationHorn ℓ0
  Ξ e = record
    { V = V
    ; B = B e
    ; PE = PE e
    ; PC = PC e }

open Equations using (E; Ξ)

sig : SigQ ℓ0 ℓ0 ℓ0 ℓ0 ℓ0
sig = record
  { S = S
  ; P = P
  ; E = E
  ; Ξ = Ξ }
