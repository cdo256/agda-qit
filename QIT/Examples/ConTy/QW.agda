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
  open EquationV
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

  PE : ∀ e → B e → EquationV V
  PE ekt̂ bkt̂-kγ .lhs = [ γ ]
  PE ekt̂ bkt̂-kγ .rhs = ĉ
  PE ek▷ bk▷-kγ .lhs = [ γ ]
  PE ek▷ bk▷-kγ .rhs = ĉ
  PE ek▷ bk▷-ka .lhs = [ a ]
  PE ek▷ bk▷-ka .rhs = t̂ γ
  PE ek▷ bk▷-kb .lhs = [ b ]
  PE ek▷ bk▷-kb .rhs = t̂ (▷ γ a)
  PE eku bku-kγ .lhs = [ γ ]
  PE eku bku-kγ .rhs = ĉ
  PE ekπ bkπ-kγ .lhs = [ γ ]
  PE ekπ bkπ-kγ .rhs = ĉ
  PE ekπ bkπ-ka .lhs = [ a ]
  PE ekπ bkπ-ka .rhs = t̂ γ
  PE ekπ bkπ-kb .lhs = [ b ]
  PE ekπ bkπ-kb .rhs = t̂ (▷ γ a)
  PE ekσ bkσ-kγ .lhs = [ γ ]
  PE ekσ bkσ-kγ .rhs = ĉ
  PE ekσ bkσ-ka .lhs = [ a ]
  PE ekσ bkσ-ka .rhs = t̂ γ
  PE ekσ bkσ-kb .lhs = [ b ]
  PE ekσ bkσ-kb .rhs = t̂ (▷ γ a)
  PE eσ▷ bσ▷-kγ .lhs = [ γ ]
  PE eσ▷ bσ▷-kγ .rhs = ĉ
  PE eσ▷ bσ▷-ka .lhs = [ a ]
  PE eσ▷ bσ▷-ka .rhs = t̂ γ
  PE eσ▷ bσ▷-kb .lhs = [ b ]
  PE eσ▷ bσ▷-kb .rhs = t̂ (▷ γ a)
  PE eσ▷ bσ▷-kc .lhs = [ c ]
  PE eσ▷ bσ▷-kc .rhs = t̂ (▷ (▷ γ a) b)
  PE eσπ bσπ-kγ .lhs = [ γ ]
  PE eσπ bσπ-kγ .rhs = ĉ
  PE eσπ bσπ-ka .lhs = [ a ]
  PE eσπ bσπ-ka .rhs = t̂ γ
  PE eσπ bσπ-kb .lhs = [ b ]
  PE eσπ bσπ-kb .rhs = t̂ (▷ γ a)
  PE eσπ bσπ-kc .lhs = [ c ]
  PE eσπ bσπ-kc .rhs = t̂ (▷ (▷ γ a) b)

  PC : E → EquationV V
  PC ekk̂ .lhs = [ k̂ ]
  PC ekk̂ .rhs = k̂
  PC ekĉ .lhs = [ ĉ ]
  PC ekĉ .rhs = k̂
  PC ekt̂ .lhs = [ t̂ γ ]
  PC ekt̂ .rhs = k̂
  PC ek∙ .lhs = [ ∙ ]
  PC ek∙ .rhs = ĉ
  PC ek▷ .lhs = [ ▷ γ a ]
  PC ek▷ .rhs = ĉ
  PC eku .lhs = [ u γ ]
  PC eku .rhs = t̂ γ
  PC ekπ .lhs = [ π γ a b ]
  PC ekπ .rhs = t̂ γ
  PC ekσ .lhs = [ σ γ a b ]
  PC ekσ .rhs = t̂ γ
  PC eσ▷ .lhs = ▷ (σ γ a b) c
  PC eσ▷ .rhs = ▷ (▷ (▷ γ a) b) c
  PC eσπ .lhs = π γ a (π (▷ γ a) b c)
  PC eσπ .rhs = π γ (σ γ a b) c

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
