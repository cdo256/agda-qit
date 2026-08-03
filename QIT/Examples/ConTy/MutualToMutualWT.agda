open import QIT.Prelude

module QIT.Examples.ConTy.MutualToMutualWT
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

open PropExt propExt*
open FunExt funExt*

import QIT.Examples.ConTy.MutualProjection as M
import QIT.Examples.ConTy.MutualWeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
open import QIT.Types
open import QIT.Maybe using (Maybe)
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Category.Base
open import QIT.PropLiftMonad

G₀ : M.Algebra ℓA → W.Algebra (lsuc ℓA)
G₀ {ℓA} da = wa
  module G₀ where
  open ≡
  open ≡.≡-Reasoning
  module MA = M.Algebra da
  data Atom : Set ℓA where
    con : MA.Con → Atom
    ty : MA.Ty → Atom
    k̂ : Atom
    ĉ : Atom
    t̂ : Atom

  mkCT≈ : {P Q : Prop ℓP} {f : P → Atom} {g : Q → Atom}
      → (p→q : P → Q) (q→p : Q → P) (f≡g : ∀ p q → f p ≡ g q)
      → (P ⊢ f) ≈ (Q ⊢ g)
  mkCT≈ p→q q→p f≡g = ∧i ∧i p→q , q→p , f≡g

  mkCT≡ : {P Q : Prop ℓP} {f : P → Atom} {g : Q → Atom}
      → (p→q : P → Q) (q→p : Q → P) (f≡g : ∀ p q → f p ≡ g q)
      → (P ⊢ f) ≡ (Q ⊢ g)
  mkCT≡ p→q q→p f≡g = ≈→≡ (∧i ∧i p→q , q→p , f≡g)

  CT = PropLift ℓA Atom

  kʰ : CT
  kʰ = return k̂
  cʰ : CT
  cʰ = return ĉ
  tʰ : CT
  tʰ = return t̂

  module EncodeAtom where
    Code : Atom → Atom → Prop ℓA
    Code (con γ) (con δ) = γ ≡ δ
    Code (ty a) (ty b) = a ≡ b
    Code k̂ k̂ = ⊤*
    Code ĉ ĉ = ⊤*
    Code t̂ t̂ = ⊤*
    {-# CATCHALL #-}
    Code _ _ = ⊥*

    reflCode : (x : Atom) → Code x x
    reflCode (con γ) = ≡.refl
    reflCode (ty a) = ≡.refl
    reflCode k̂ = tt*
    reflCode ĉ = tt*
    reflCode t̂ = tt*

    encode : ∀ {x y} → x ≡ y → Code x y
    encode {x} refl = reflCode x

    decode : ∀ {x y} → Code x y → x ≡ y
    decode {con γ} {con δ} p = ≡.cong con p
    decode {ty a} {ty b} ( q) = ≡.cong ty q
    decode {k̂} {k̂} p = refl
    decode {ĉ} {ĉ} p = refl
    decode {t̂} {t̂} p = refl

    k̂≢ĉ : k̂ ≢ ĉ
    k̂≢ĉ p = ⊥e* (encode p)

    k̂≢t̂ : k̂ ≢ t̂
    k̂≢t̂ p = ⊥e* (encode p)

    ĉ≢t̂ : ĉ ≢ t̂
    ĉ≢t̂ p = ⊥e* (encode p)

  open EncodeAtom public

  kʰ≢cʰ : kʰ ≢ cʰ
  kʰ≢cʰ p = k̂≢ĉ (return-inj p)

  kʰ≢tʰ : kʰ ≢ tʰ
  kʰ≢tʰ p = k̂≢t̂ (return-inj p)
    
  cʰ≢tʰ : cʰ ≢ tʰ
  cʰ≢tʰ p = ĉ≢t̂ (return-inj p)

  [_]₀ : Atom → Atom
  [ con γ ]₀ = ĉ
  [ ty a ]₀ = t̂
  [ k̂ ]₀ = k̂
  [ ĉ ]₀ = k̂
  [ t̂ ]₀ = k̂

  ty₁₀ : ∀ a → [ a ]₀ ≡ t̂ → Atom
  ty₁₀ (ty a) ka = con (MA.ty₁ a)

  [[x]]₀≡k̂ : ∀ x → [ [ x ]₀ ]₀ ≡ k̂
  [[x]]₀≡k̂ (con γ) = refl
  [[x]]₀≡k̂ (ty a) = refl
  [[x]]₀≡k̂ k̂ = refl
  [[x]]₀≡k̂ ĉ = refl
  [[x]]₀≡k̂ t̂ = refl

  [k̂]₀≡k̂ : [ k̂ ]₀ ≡ k̂
  [k̂]₀≡k̂ = refl

  [_] : CT → CT
  [_] = map [_]₀

  ty₁ : CT → CT
  ty₁ a* =
    a* >>= λ a →
    assume ([ a ]₀ ≡ t̂) λ ka →
    return (ty₁₀ a ka)

  con-inj : ∀ {γ δ} → con γ ≡ con δ → γ ≡ δ
  con-inj refl = refl

  ty-inj : ∀ {a b : MA.Ty} → ty a ≡ ty b → a ≡ b
  ty-inj refl = refl

  []₀≡ĉ→con : ∀ {x} → [ x ]₀ ≡ ĉ
    → ΣP MA.Con λ γ
    → x ≡ con γ
  []₀≡ĉ→con {con γ} p = γ , refl

  []₀≡t̂→ty : ∀ {x} → [ x ]₀ ≡ t̂
    → ΣP MA.Ty λ a
    → x ≡ ty a
  []₀≡t̂→ty {ty a} p = a , refl

  ConΣ = ΣP Atom λ γ → [ γ ]₀ ≡ ĉ
  ConΣ→Con : ConΣ → MA.Con
  ConΣ→Con (con γ , kγ) = γ
  Con→ConΣ : MA.Con → ConΣ
  Con→ConΣ γ = (con γ , refl)
  TyΣ : Set ℓA
  TyΣ = ΣP Atom λ a → [ a ]₀ ≡ t̂
  TyΣ→Ty : TyΣ → MA.Ty
  TyΣ→Ty (ty a , ka) = a
  Ty→TyΣ : MA.Ty → TyΣ
  Ty→TyΣ a = ty a , refl

  ConΣ≅Con : ConΣ ≅ˢ MA.Con
  ConΣ≅Con = record
    { to = ConΣ→Con
    ; from = Con→ConΣ
    ; rinv = λ {(con γ , refl) → refl}
    ; linv = λ γ → refl }

  []⁻ : ∀ x* → [ x* ] ↓ → x* ↓
  []⁻ x* [x]↓ = [x]↓ .∧e₂

  ty₁⁻ : ∀ x* → ty₁ x* ↓ → x* ↓
  ty₁⁻ x* ty↓ = ty↓ .∧e₁

  []≡cʰ→return
    : ∀ {x*}
    → [ x* ] ≡ cʰ
    → ΣP MA.Con λ γ
    → x* ≡ return (con γ)
  []≡cʰ→return {x*} p = γ , x*≡returnγ
    where
    p≈ : [ x* ] ≈ cʰ
    p≈ = ≡→≈ p
    x↓ : x* ↓
    x↓ = p≈ .∧e₁ .∧e₂ tt* .∧e₂
    x : Atom
    x = x* ! x↓
    kx : [ x ]₀ ≡ ĉ
    kx = p≈ .∧e₂ (∧i tt* , x↓) tt*
    γ : MA.Con
    γ = []₀≡ĉ→con kx .fst
    x≡conγ : x ≡ con γ
    x≡conγ = []₀≡ĉ→con kx .snd
    x*≡returnγ : x* ≡ return (con γ)
    x*≡returnγ = mk≡↓ x↓ tt* x≡conγ

  []≡tʰ→return
    : ∀ {x*}
    → [ x* ] ≡ tʰ
    → ΣP MA.Ty λ a
    → x* ≡ return (ty a)
  []≡tʰ→return {x*} p = a , x*≡return
    where
    p≈ : [ x* ] ≈ tʰ
    p≈ = ≡→≈ p
    x↓ : x* ↓
    x↓ = p≈ .∧e₁ .∧e₂ tt* .∧e₂
    x : Atom
    x = x* ! x↓
    kx : [ x ]₀ ≡ t̂
    kx = p≈ .∧e₂ (∧i tt* , x↓) tt*
    a : MA.Ty
    a = []₀≡t̂→ty kx .fst
    x≡ty : x ≡ ty a
    x≡ty = []₀≡t̂→ty kx .snd
    x*≡return : x* ≡ return (ty a)
    x*≡return = mk≡↓ x↓ tt* x≡ty

  kty₁ : ∀ a* → [ a* ] ≡ tʰ → [ ty₁ a* ] ≡ cʰ
  kty₁ a* ka = mk≡↓ {!!} tt* {!!}
    where
    a↓ : a* ↓
    a↓ = []⁻ a* (transp↓⁻ ka tt*)
    w : ΣP MA.Ty λ a → a* ≡ return (ty a)
    w = []≡tʰ→return ka
    ty↓ : ty₁ a* ↓
    ty↓ = ∧i a↓ , (∧i (transp!⁻ ka tt*) , tt*)

  Con₀ : (γ : Atom) → [ γ ]₀ ≡ ĉ → MA.Con
  Con₀ γ kγ = ConΣ→Con (γ , kγ)

  con-Con₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → con (Con₀ γ kγ) ≡ γ
  con-Con₀ (con γ) refl = refl

  Ty₀ : (a : Atom) → [ a ]₀ ≡ t̂ → MA.Ty
  Ty₀ a ka = TyΣ→Ty (a , ka)

  ∙₀ : Atom
  ∙₀ = con MA.∙

  ▷₀ : (γ a : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → (ka : [ a ]₀ ≡ t̂) → ty₁₀ a ka ≡ γ → Atom
  ▷₀ (con γ) (ty a) kγ ka a₁ = con (MA.▷ γ a (con-inj a₁))

  k▷₀ : (γ a : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → [ ▷₀ γ a kγ ka a₁ ]₀ ≡ ĉ
  k▷₀ (con γ) (ty a) kγ ka a₁ = refl

  ▷Σ : (γ : ConΣ) → (a : TyΣ) → ty₁₀ (a .fst) (a .snd) ≡ γ .fst → ConΣ
  ▷Σ (γ , kγ) (a , ka) a₁ = ▷₀ γ a kγ ka a₁ , k▷₀ γ a kγ ka a₁

  ty₁₀-Ty₀ : (a : Atom) → (ka : [ a ]₀ ≡ t̂)
    → con (MA.ty₁ (Ty₀ a ka)) ≡ ty₁₀ a ka
  ty₁₀-Ty₀ (ty a) refl = refl

  Ty₀₁ : (γ a : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → ty₁₀ a ka ≡ γ
    → MA.ty₁ (Ty₀ a ka) ≡ Con₀ γ kγ
  Ty₀₁ γ a kγ ka a₁ =
    con-inj (trans (ty₁₀-Ty₀ a ka) (trans a₁ (sym (con-Con₀ γ kγ))))

  Con₀-▷₀ : (γ a : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → Con₀ (▷₀ γ a kγ ka a₁) (k▷₀ γ a kγ ka a₁)
      ≡ MA.▷ (Con₀ γ kγ) (Ty₀ a ka) (Ty₀₁ γ a kγ ka a₁)
  Con₀-▷₀ (con γ) (ty a) kγ ka a₁ = refl

  u₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → Atom
  u₀ γ kγ = ty (MA.u (Con₀ γ kγ))

  ku₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → [ u₀ γ kγ ]₀ ≡ t̂
  ku₀ γ kγ = refl

  u₁₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ)
    → ty₁₀ (u₀ γ kγ) (ku₀ γ kγ) ≡ γ
  u₁₀ γ kγ =
    trans
      (sym (ty₁₀-Ty₀ (u₀ γ kγ) (ku₀ γ kγ)))
      (trans (cong con (MA.u₁ (Con₀ γ kγ))) (con-Con₀ γ kγ))

  π₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → Atom
  π₀ γ a b kγ ka a₁ kb b₁ =
    ty (MA.π (Con₀ γ kγ)
             (Ty₀ a ka)
             (Ty₀ b kb)
             (Ty₀₁ γ a kγ ka a₁)
             (trans (Ty₀₁ (▷₀ γ a kγ ka a₁) b (k▷₀ γ a kγ ka a₁) kb b₁)
                    (Con₀-▷₀ γ a kγ ka a₁)))

  kπ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → [ π₀ γ a b kγ ka a₁ kb b₁ ]₀ ≡ t̂
  kπ₀ γ a b kγ ka a₁ kb b₁ = refl

  π₁₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → ty₁₀ (π₀ γ a b kγ ka a₁ kb b₁) (kπ₀ γ a b kγ ka a₁ kb b₁) ≡ γ
  π₁₀ γ a b kγ ka a₁ kb b₁ =
    trans
      (sym (ty₁₀-Ty₀ (π₀ γ a b kγ ka a₁ kb b₁) (kπ₀ γ a b kγ ka a₁ kb b₁)))
      (trans
        (cong con
          (MA.π₁ (Con₀ γ kγ)
                (Ty₀ a ka)
                (Ty₀ b kb)
                (Ty₀₁ γ a kγ ka a₁)
                (trans (Ty₀₁ (▷₀ γ a kγ ka a₁) b (k▷₀ γ a kγ ka a₁) kb b₁)
                       (Con₀-▷₀ γ a kγ ka a₁))))
        (con-Con₀ γ kγ))

  σ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → Atom
  σ₀ γ a b kγ ka a₁ kb b₁ =
    ty (MA.σ (Con₀ γ kγ)
             (Ty₀ a ka)
             (Ty₀ b kb)
             (Ty₀₁ γ a kγ ka a₁)
             (trans (Ty₀₁ (▷₀ γ a kγ ka a₁) b (k▷₀ γ a kγ ka a₁) kb b₁)
                    (Con₀-▷₀ γ a kγ ka a₁)))

  kσ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → [ σ₀ γ a b kγ ka a₁ kb b₁ ]₀ ≡ t̂
  kσ₀ γ a b kγ ka a₁ kb b₁ = refl

  σ₁₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → ty₁₀ (σ₀ γ a b kγ ka a₁ kb b₁) (kσ₀ γ a b kγ ka a₁ kb b₁) ≡ γ
  σ₁₀ γ a b kγ ka a₁ kb b₁ =
    trans
      (sym (ty₁₀-Ty₀ (σ₀ γ a b kγ ka a₁ kb b₁) (kσ₀ γ a b kγ ka a₁ kb b₁)))
      (trans
        (cong con
          (MA.σ₁ (Con₀ γ kγ)
                (Ty₀ a ka)
                (Ty₀ b kb)
                (Ty₀₁ γ a kγ ka a₁)
                (trans (Ty₀₁ (▷₀ γ a kγ ka a₁) b (k▷₀ γ a kγ ka a₁) kb b₁)
                       (Con₀-▷₀ γ a kγ ka a₁))))
        (con-Con₀ γ kγ))

  σ▷₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → ▷₀ (▷₀ γ a kγ ka a₁) b (k▷₀ γ a kγ ka a₁) kb b₁
    ≡ ▷₀ γ (σ₀ γ a b kγ ka a₁ kb b₁) kγ (kσ₀ γ a b kγ ka a₁ kb b₁) (σ₁₀ γ a b kγ ka a₁ kb b₁)
  σ▷₀ (con γ) (ty a) (ty b) kγ ka a₁ kb b₁ =
    cong con
      (MA.σ▷ (Con₀ (con γ) kγ)
             (Ty₀ (ty a) ka)
             (Ty₀ (ty b) kb)
             (Ty₀₁ (con γ) (ty a) kγ ka a₁)
             (trans (Ty₀₁ (▷₀ (con γ) (ty a) kγ ka a₁) (ty b) (k▷₀ (con γ) (ty a) kγ ka a₁) kb b₁)
                    (Con₀-▷₀ (con γ) (ty a) kγ ka a₁)))

  σπ₀ : (γ a b d : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂)
    → (a₁ : ty₁₀ a ka ≡ γ)
    → (kb : [ b ]₀ ≡ t̂)
    → (b₁ : ty₁₀ b kb ≡ ▷₀ γ a kγ ka a₁)
    → (kd : [ d ]₀ ≡ t̂)
    → (d₁ : ty₁₀ d kd ≡ ▷₀ (▷₀ γ a kγ ka a₁) b (k▷₀ γ a kγ ka a₁) kb b₁)
    → π₀ γ a (π₀ (▷₀ γ a kγ ka a₁) b d (k▷₀ γ a kγ ka a₁) kb b₁ kd d₁)
         kγ ka a₁ (kπ₀ (▷₀ γ a kγ ka a₁) b d (k▷₀ γ a kγ ka a₁) kb b₁ kd d₁)
         (π₁₀ (▷₀ γ a kγ ka a₁) b d (k▷₀ γ a kγ ka a₁) kb b₁ kd d₁)
      ≡ π₀ γ (σ₀ γ a b kγ ka a₁ kb b₁) d
         kγ (kσ₀ γ a b kγ ka a₁ kb b₁) (σ₁₀ γ a b kγ ka a₁ kb b₁)
         kd
         (trans d₁ (σ▷₀ γ a b kγ ka a₁ kb b₁))
  σπ₀ (con γ) (ty a) (ty b) (ty d) kγ ka a₁ kb b₁ kd d₁ =
    cong ty
      (MA.σπ (Con₀ (con γ) kγ)
             (Ty₀ (ty a) ka)
             (Ty₀ (ty b) kb)
             (Ty₀ (ty d) kd)
             (Ty₀₁ (con γ) (ty a) kγ ka a₁)
             (trans (Ty₀₁ (▷₀ (con γ) (ty a) kγ ka a₁) (ty b) (k▷₀ (con γ) (ty a) kγ ka a₁) kb b₁)
                    (Con₀-▷₀ (con γ) (ty a) kγ ka a₁))
             (Ty₀₁ (▷₀ (▷₀ (con γ) (ty a) kγ ka a₁) (ty b) (k▷₀ (con γ) (ty a) kγ ka a₁) kb b₁) (ty d)
                   (k▷₀ (▷₀ (con γ) (ty a) kγ ka a₁) (ty b) (k▷₀ (con γ) (ty a) kγ ka a₁) kb b₁) kd d₁))

  con↓ : (γʰ : CT) → [ γʰ ] ≡ cʰ → γʰ ↓
  con↓ γʰ kγ = transp↓⁻ kγ tt* .∧e₂

  getConAtom : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → Atom
  getConAtom γʰ kγ = γʰ ! (con↓ γʰ kγ)

  conKind : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → [ getConAtom γʰ kγ ]₀ ≡ ĉ
  conKind γʰ kγ = transp!⁻ kγ tt*

  getConΣ : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → ConΣ
  getConΣ γʰ kγ = getConAtom γʰ kγ , conKind γʰ kγ

  getCon : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → MA.Con
  getCon γʰ kγ = ConΣ→Con (getConΣ γʰ kγ)

  ty↓ : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → aʰ ↓
  ty↓ aʰ ka = transp↓⁻ ka tt* .∧e₂

  []↓ : ∀ x → x ↓ → [ x ] ↓
  []↓ x x↓ = ∧i tt* , x↓

  getTyAtom : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → Atom
  getTyAtom aʰ ka = aʰ ! (ty↓ aʰ ka)

  tyKind : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → [ getTyAtom aʰ ka ]₀ ≡ t̂
  tyKind aʰ ka = transp!⁻ ka tt*

  ty₁↓ : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → ty₁ aʰ ↓
  ty₁↓ aʰ ka = ∧i ty↓ aʰ ka , ∧i tyKind aʰ ka , tt*

  getTy₁-kind : (γʰ aʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ)
    → (ka₁ : ty₁ aʰ ≡ γʰ)
    → ty₁₀ (getTyAtom aʰ ka) (tyKind aʰ ka) ≡ getConAtom γʰ kγ
  getTy₁-kind γʰ aʰ kγ ka ka₁ = transp!⁻ ka₁ (con↓ γʰ kγ)

  getTyΣ : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → TyΣ
  getTyΣ aʰ ka = getTyAtom aʰ ka , tyKind aʰ ka

  getTy : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → MA.Ty
  getTy aʰ ka = TyΣ→Ty (getTyΣ aʰ ka)

  ∙ : CT
  ∙ = return ∙₀

  ▷ : CT → CT → CT
  ▷ γʰ aʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂) λ ka →
    assume (ty₁₀ a ka ≡ γ) λ ka₁ →
    return (▷₀ γ a kγ ka ka₁)

  ▷⁻-γ : ∀ γʰ aʰ → (▷ γʰ aʰ) ↓ → γʰ ↓
  ▷⁻-γ γʰ aʰ ▷↓ = ▷↓ .∧e₁

  ▷⁻-a : ∀ γʰ aʰ → (▷ γʰ aʰ) ↓ → aʰ ↓
  ▷⁻-a γʰ aʰ ▷↓ = ▷↓ .∧e₂ .∧e₁

  ▷⁻-kγ : ∀ γʰ aʰ → (▷↓ : ▷ γʰ aʰ ↓) → [ γʰ ! (▷⁻-γ γʰ aʰ ▷↓) ]₀ ≡ ĉ
  ▷⁻-kγ γʰ aʰ ▷↓ = ▷↓ .∧e₂ .∧e₂ .∧e₁

  ▷⁻-ka : ∀ γʰ aʰ → (▷↓ : ▷ γʰ aʰ ↓) → [ aʰ ! (▷⁻-a γʰ aʰ ▷↓) ]₀ ≡ t̂
  ▷⁻-ka γʰ aʰ ▷↓ = ▷↓ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  ▷⁻-ka₁ : ∀ γʰ aʰ
    → (▷↓ : ▷ γʰ aʰ ↓)
    → ty₁₀ (aʰ ! (▷⁻-a γʰ aʰ ▷↓)) (▷⁻-ka γʰ aʰ ▷↓)
      ≡ γʰ ! (▷⁻-γ γʰ aʰ ▷↓)
  ▷⁻-ka₁ γʰ aʰ ▷↓ = ▷↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  ▷≡return : ∀ γ̂ â
    → (kγ : [ γ̂ ]₀ ≡ ĉ)
    → (ka : [ â ]₀ ≡ t̂)
    → (ka₁ : ty₁₀ â ka ≡ γ̂)
    → ▷ (return γ̂) (return â) ≡ return (▷₀ γ̂ â kγ ka ka₁)
  ▷≡return γ̂ â kγ ka ka₁ =
    mk≡↓ (∧i tt* , ∧i tt* , ∧i kγ , ∧i ka , ∧i ka₁ , tt*) tt* refl

  u : CT → CT
  u γʰ =
    γʰ >>= λ γ →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    return (u₀ γ kγ)

  u⁻-γ : ∀ γʰ → u γʰ ↓ → γʰ ↓
  u⁻-γ γʰ u↓ = u↓ .∧e₁

  u⁻-kγ : ∀ γʰ → (u↓ : u γʰ ↓) → [ γʰ ! (u⁻-γ γʰ u↓) ]₀ ≡ ĉ
  u⁻-kγ γʰ u↓ = u↓ .∧e₂ .∧e₁

  ku : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ u γʰ ] ≡ tʰ
  ku γʰ kγ = mk≡↓ (∧i tt* , ∧i con↓ γʰ kγ , ∧i conKind γʰ kγ , tt*) tt* refl

  u₁ : (γʰ : CT) → [ γʰ ] ≡ cʰ → ty₁ (u γʰ) ≡ γʰ
  u₁ γʰ kγ = mk≡↓ l↓ r↓ val≡
    where
    l↓ : ty₁ (u γʰ) ↓
    l↓ = ∧i (∧i con↓ γʰ kγ , ∧i conKind γʰ kγ , tt*) , ∧i transp!⁻ (ku γʰ kγ) tt* , tt*
    r↓ : γʰ ↓
    r↓ = con↓ γʰ kγ
    val≡ : ty₁ (u γʰ) ! l↓ ≡ γʰ ! r↓
    val≡ = u₁₀ (γʰ ! r↓) (conKind γʰ kγ)

  π : CT → CT → CT → CT
  π γʰ aʰ bʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    bʰ >>= λ b →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂) λ ka →
    assume (ty₁₀ a ka ≡ γ) λ ka₁ →
    assume ([ b ]₀ ≡ t̂) λ kb →
    assume (ty₁₀ b kb ≡ ▷₀ γ a kγ ka ka₁) λ kb₁ →
    return (π₀ γ a b kγ ka ka₁ kb kb₁)

  π⁻-γ : ∀ γʰ aʰ bʰ → π γʰ aʰ bʰ ↓ → γʰ ↓
  π⁻-γ γʰ aʰ bʰ π↓ = π↓ .∧e₁

  π⁻-a : ∀ γʰ aʰ bʰ → π γʰ aʰ bʰ ↓ → aʰ ↓
  π⁻-a γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₁

  π⁻-b : ∀ γʰ aʰ bʰ → π γʰ aʰ bʰ ↓ → bʰ ↓
  π⁻-b γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₁

  π⁻-kγ : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → [ γʰ ! (π⁻-γ γʰ aʰ bʰ π↓) ]₀ ≡ ĉ
  π⁻-kγ γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  π⁻-ka : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → [ aʰ ! (π⁻-a γʰ aʰ bʰ π↓) ]₀ ≡ t̂
  π⁻-ka γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  π⁻-ka₁ : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → ty₁₀ (aʰ ! (π⁻-a γʰ aʰ bʰ π↓)) (π⁻-ka γʰ aʰ bʰ π↓)
      ≡ γʰ ! (π⁻-γ γʰ aʰ bʰ π↓)
  π⁻-ka₁ γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  π⁻-kb : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → [ bʰ ! (π⁻-b γʰ aʰ bʰ π↓) ]₀ ≡ t̂
  π⁻-kb γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  π⁻-kb₁ : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → ty₁₀ (bʰ ! (π⁻-b γʰ aʰ bʰ π↓)) (π⁻-kb γʰ aʰ bʰ π↓)
      ≡ ▷₀ (γʰ ! (π⁻-γ γʰ aʰ bʰ π↓))
           (aʰ ! (π⁻-a γʰ aʰ bʰ π↓))
           (π⁻-kγ γʰ aʰ bʰ π↓)
           (π⁻-ka γʰ aʰ bʰ π↓)
           (π⁻-ka₁ γʰ aʰ bʰ π↓)
  π⁻-kb₁ γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  σ : CT → CT → CT → CT
  σ γʰ aʰ bʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    bʰ >>= λ b →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂) λ ka →
    assume (ty₁₀ a ka ≡ γ) λ ka₁ →
    assume ([ b ]₀ ≡ t̂) λ kb →
    assume (ty₁₀ b kb ≡ ▷₀ γ a kγ ka ka₁) λ kb₁ →
    return (σ₀ γ a b kγ ka ka₁ kb kb₁)

  σ⁻-γ : ∀ γʰ aʰ bʰ → σ γʰ aʰ bʰ ↓ → γʰ ↓
  σ⁻-γ γʰ aʰ bʰ σ↓ = σ↓ .∧e₁

  σ⁻-a : ∀ γʰ aʰ bʰ → σ γʰ aʰ bʰ ↓ → aʰ ↓
  σ⁻-a γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₁

  σ⁻-b : ∀ γʰ aʰ bʰ → σ γʰ aʰ bʰ ↓ → bʰ ↓
  σ⁻-b γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₁

  σ⁻-kγ : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → [ γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓) ]₀ ≡ ĉ
  σ⁻-kγ γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  σ⁻-ka : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → [ aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓) ]₀ ≡ t̂
  σ⁻-ka γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  σ⁻-ka₁ : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → ty₁₀ (aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓)) (σ⁻-ka γʰ aʰ bʰ σ↓)
      ≡ γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓)
  σ⁻-ka₁ γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  σ⁻-kb : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → [ bʰ ! (σ⁻-b γʰ aʰ bʰ σ↓) ]₀ ≡ t̂
  σ⁻-kb γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  σ⁻-kb₁ : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → ty₁₀ (bʰ ! (σ⁻-b γʰ aʰ bʰ σ↓)) (σ⁻-kb γʰ aʰ bʰ σ↓)
      ≡ ▷₀ (γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓))
           (aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓))
           (σ⁻-kγ γʰ aʰ bʰ σ↓)
           (σ⁻-ka γʰ aʰ bʰ σ↓)
           (σ⁻-ka₁ γʰ aʰ bʰ σ↓)
  σ⁻-kb₁ γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  k∙ : [ ∙ ] ≡ cʰ
  k∙ = mk≡↓ (∧i tt* , tt*) tt* refl

  k▷ : (γʰ aʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ
    → ty₁ aʰ ≡ γʰ
    → [ ▷ γʰ aʰ ] ≡ cʰ
  k▷ γʰ aʰ kγ ka ka₁ = mk≡↓ q tt* val≡
    where
    q : [ ▷ γʰ aʰ ] ↓
    q = ∧i tt* , ∧i con↓ γʰ kγ , ∧i ty↓ aʰ ka , ∧i conKind γʰ kγ , ∧i tyKind aʰ ka , ∧i getTy₁-kind γʰ aʰ kγ ka ka₁ , tt*
    val≡ : [ ▷ γʰ aʰ ] ! q ≡ cʰ ! tt*
    val≡ = k▷₀ (γʰ ! (con↓ γʰ kγ)) (aʰ ! (ty↓ aʰ ka)) (conKind γʰ kγ) (tyKind aʰ ka) (getTy₁-kind γʰ aʰ kγ ka ka₁)

  kπ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ
    → ty₁ aʰ ≡ γʰ
    → [ bʰ ] ≡ tʰ
    → ty₁ bʰ ≡ ▷ γʰ aʰ
    → [ π γʰ aʰ bʰ ] ≡ tʰ
  kπ γʰ aʰ bʰ kγ ka ka₁ kb kb₁ = mk≡↓ l↓ tt* val≡
    where
    π↓ : π γʰ aʰ bʰ ↓
    π↓ = ∧i con↓ γʰ kγ , ∧i ty↓ aʰ ka , ∧i ty↓ bʰ kb , ∧i conKind γʰ kγ , ∧i tyKind aʰ ka , ∧i getTy₁-kind γʰ aʰ kγ ka ka₁ , ∧i tyKind bʰ kb , ∧i getTy₁-kind (▷ γʰ aʰ) bʰ (k▷ γʰ aʰ kγ ka ka₁) kb kb₁ , tt*
    l↓ : [ π γʰ aʰ bʰ ] ↓
    l↓ = ∧i tt* , ∧i π⁻-γ γʰ aʰ bʰ π↓ , ∧i π⁻-a γʰ aʰ bʰ π↓ , ∧i π⁻-b γʰ aʰ bʰ π↓ , ∧i π⁻-kγ γʰ aʰ bʰ π↓ , ∧i π⁻-ka γʰ aʰ bʰ π↓ , ∧i π⁻-ka₁ γʰ aʰ bʰ π↓ , ∧i π⁻-kb γʰ aʰ bʰ π↓ , ∧i π⁻-kb₁ γʰ aʰ bʰ π↓ , tt*
    val≡ : [ π γʰ aʰ bʰ ] ! l↓ ≡ tʰ ! tt*
    val≡ = kπ₀ (γʰ ! (π⁻-γ γʰ aʰ bʰ π↓)) (aʰ ! (π⁻-a γʰ aʰ bʰ π↓)) (bʰ ! (π⁻-b γʰ aʰ bʰ π↓)) (π⁻-kγ γʰ aʰ bʰ π↓) (π⁻-ka γʰ aʰ bʰ π↓) (π⁻-ka₁ γʰ aʰ bʰ π↓) (π⁻-kb γʰ aʰ bʰ π↓) (π⁻-kb₁ γʰ aʰ bʰ π↓)

  π₁ : (γʰ aʰ bʰ : CT)
    → [ π γʰ aʰ bʰ ] ≡ tʰ
    → ty₁ (π γʰ aʰ bʰ) ≡ γʰ
  π₁ γʰ aʰ bʰ kπ = mk≡↓ l↓ r↓ val≡
    where
    mutual
      [πγab]↓ : [ π γʰ aʰ bʰ ] ↓
      [πγab]↓ = transp↓⁻ kπ tt*
      π↓ : π γʰ aʰ bʰ ↓
      π↓ = []⁻ (π γʰ aʰ bʰ) [πγab]↓
      l↓ : ty₁ (π γʰ aʰ bʰ) ↓
      l↓ = ∧i π↓ , ∧i transp!⁻ kπ tt* , tt*
      r↓ : γʰ ↓
      r↓ = π⁻-γ γʰ aʰ bʰ π↓
      val≡ : ty₁ (π γʰ aʰ bʰ) ! l↓ ≡ γʰ ! r↓
      val≡ = π₁₀ (γʰ ! r↓) (aʰ ! (π⁻-a γʰ aʰ bʰ π↓)) (bʰ ! (π⁻-b γʰ aʰ bʰ π↓)) (π⁻-kγ γʰ aʰ bʰ π↓) (π⁻-ka γʰ aʰ bʰ π↓) (π⁻-ka₁ γʰ aʰ bʰ π↓) (π⁻-kb γʰ aʰ bʰ π↓) (π⁻-kb₁ γʰ aʰ bʰ π↓)

  kσ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ
    → ty₁ aʰ ≡ γʰ
    → [ bʰ ] ≡ tʰ
    → ty₁ bʰ ≡ ▷ γʰ aʰ
    → [ σ γʰ aʰ bʰ ] ≡ tʰ
  kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁ = mk≡↓ l↓ tt* val≡
    where
    σ↓ : σ γʰ aʰ bʰ ↓
    σ↓ = ∧i con↓ γʰ kγ , ∧i ty↓ aʰ ka , ∧i ty↓ bʰ kb , ∧i conKind γʰ kγ , ∧i tyKind aʰ ka , ∧i getTy₁-kind γʰ aʰ kγ ka ka₁ , ∧i tyKind bʰ kb , ∧i getTy₁-kind (▷ γʰ aʰ) bʰ (k▷ γʰ aʰ kγ ka ka₁) kb kb₁ , tt*
    l↓ : [ σ γʰ aʰ bʰ ] ↓
    l↓ = ∧i tt* , ∧i σ⁻-γ γʰ aʰ bʰ σ↓ , ∧i σ⁻-a γʰ aʰ bʰ σ↓ , ∧i σ⁻-b γʰ aʰ bʰ σ↓ , ∧i σ⁻-kγ γʰ aʰ bʰ σ↓ , ∧i σ⁻-ka γʰ aʰ bʰ σ↓ , ∧i σ⁻-ka₁ γʰ aʰ bʰ σ↓ , ∧i σ⁻-kb γʰ aʰ bʰ σ↓ , ∧i σ⁻-kb₁ γʰ aʰ bʰ σ↓ , tt*
    val≡ : [ σ γʰ aʰ bʰ ] ! l↓ ≡ tʰ ! tt*
    val≡ = kσ₀ (γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓)) (aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓)) (bʰ ! (σ⁻-b γʰ aʰ bʰ σ↓)) (σ⁻-kγ γʰ aʰ bʰ σ↓) (σ⁻-ka γʰ aʰ bʰ σ↓) (σ⁻-ka₁ γʰ aʰ bʰ σ↓) (σ⁻-kb γʰ aʰ bʰ σ↓) (σ⁻-kb₁ γʰ aʰ bʰ σ↓)

  σ₁ : (γʰ aʰ bʰ : CT)
    → [ σ γʰ aʰ bʰ ] ≡ tʰ
    → ty₁ (σ γʰ aʰ bʰ) ≡ γʰ
  σ₁ γʰ aʰ bʰ kσ = mk≡↓ l↓ r↓ val≡
    where
    mutual
      [σγab]↓ : [ σ γʰ aʰ bʰ ] ↓
      [σγab]↓ = transp↓⁻ kσ tt*
      σ↓ : σ γʰ aʰ bʰ ↓
      σ↓ = []⁻ (σ γʰ aʰ bʰ) [σγab]↓
      l↓ : ty₁ (σ γʰ aʰ bʰ) ↓
      l↓ = ∧i σ↓ , ∧i transp!⁻ kσ tt* , tt*
      r↓ : γʰ ↓
      r↓ = σ⁻-γ γʰ aʰ bʰ σ↓
      val≡ : ty₁ (σ γʰ aʰ bʰ) ! l↓ ≡ γʰ ! r↓
      val≡ = σ₁₀ (γʰ ! r↓) (aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓)) (bʰ ! (σ⁻-b γʰ aʰ bʰ σ↓)) (σ⁻-kγ γʰ aʰ bʰ σ↓) (σ⁻-ka γʰ aʰ bʰ σ↓) (σ⁻-ka₁ γʰ aʰ bʰ σ↓) (σ⁻-kb γʰ aʰ bʰ σ↓) (σ⁻-kb₁ γʰ aʰ bʰ σ↓)

  σ▷ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ
    → ty₁ aʰ ≡ γʰ
    → [ bʰ ] ≡ tʰ
    → ty₁ bʰ ≡ ▷ γʰ aʰ
    → ▷ (▷ γʰ aʰ) bʰ ≡ ▷ γʰ (σ γʰ aʰ bʰ)
  σ▷ γʰ aʰ bʰ kγ ka ka₁ kb kb₁ = mk≡↓ pq qq val≡
    where
    kδ : [ ▷ γʰ aʰ ] ≡ cʰ
    kδ = k▷ γʰ aʰ kγ ka ka₁
    qq : ▷ γʰ (σ γʰ aʰ bʰ) ↓
    qq = ∧i con↓ γʰ kγ , ∧i ty↓ (σ γʰ aʰ bʰ) (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) , ∧i conKind γʰ kγ , ∧i tyKind (σ γʰ aʰ bʰ) (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) , ∧i getTy₁-kind γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) (σ₁ γʰ aʰ bʰ (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁)) , tt*
    pq : ▷ (▷ γʰ aʰ) bʰ ↓
    pq = ∧i con↓ (▷ γʰ aʰ) kδ , ∧i ty↓ bʰ kb , ∧i conKind (▷ γʰ aʰ) kδ , ∧i tyKind bʰ kb , ∧i getTy₁-kind (▷ γʰ aʰ) bʰ kδ kb kb₁ , tt*
    val≡ : ▷ (▷ γʰ aʰ) bʰ ! pq ≡ ▷ γʰ (σ γʰ aʰ bʰ) ! qq
    val≡ = σ▷₀ (γʰ ! (con↓ γʰ kγ)) (aʰ ! (ty↓ aʰ ka)) (bʰ ! (ty↓ bʰ kb)) (conKind γʰ kγ) (tyKind aʰ ka) (getTy₁-kind γʰ aʰ kγ ka ka₁) (tyKind bʰ kb) (getTy₁-kind (▷ γʰ aʰ) bʰ kδ kb kb₁)

  σπ : (γʰ aʰ bʰ dʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ
    → ty₁ aʰ ≡ γʰ
    → [ bʰ ] ≡ tʰ
    → ty₁ bʰ ≡ ▷ γʰ aʰ
    → [ dʰ ] ≡ tʰ
    → ty₁ dʰ ≡ ▷ (▷ γʰ aʰ) bʰ
    → π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ≡ π γʰ (σ γʰ aʰ bʰ) dʰ
  σπ γʰ aʰ bʰ dʰ kγ ka ka₁ kb kb₁ kc kc₁ = mk≡↓ pq qq val≡
    where
    kδ : [ ▷ γʰ aʰ ] ≡ cʰ
    kδ = k▷ γʰ aʰ kγ ka ka₁
    kε : [ ▷ (▷ γʰ aʰ) bʰ ] ≡ cʰ
    kε = k▷ (▷ γʰ aʰ) bʰ kδ kb kb₁
    qq : π γʰ (σ γʰ aʰ bʰ) dʰ ↓
    qq = ∧i con↓ γʰ kγ , ∧i ty↓ (σ γʰ aʰ bʰ) (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) , ∧i ty↓ dʰ kc , ∧i conKind γʰ kγ , ∧i tyKind (σ γʰ aʰ bʰ) (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) , ∧i getTy₁-kind γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) (σ₁ γʰ aʰ bʰ (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁)) , ∧i tyKind dʰ kc , ∧i getTy₁-kind (▷ γʰ (σ γʰ aʰ bʰ)) dʰ (k▷ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) (σ₁ γʰ aʰ bʰ (kσ γʰ aʰ bʰ kγ ka ka₁ kb kb₁))) kc (substp (λ x → ty₁ dʰ ≡ x) (σ▷ γʰ aʰ bʰ kγ ka ka₁ kb kb₁) kc₁) , tt*
    pq : π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ↓
    pq = ∧i con↓ γʰ kγ , ∧i ty↓ aʰ ka , ∧i ty↓ (π (▷ γʰ aʰ) bʰ dʰ) (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kb₁ kc kc₁) , ∧i conKind γʰ kγ , ∧i tyKind aʰ ka , ∧i getTy₁-kind γʰ aʰ kγ ka ka₁ , ∧i tyKind (π (▷ γʰ aʰ) bʰ dʰ) (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kb₁ kc kc₁) , ∧i getTy₁-kind (▷ γʰ aʰ) (π (▷ γʰ aʰ) bʰ dʰ) kδ (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kb₁ kc kc₁) (π₁ (▷ γʰ aʰ) bʰ dʰ (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kb₁ kc kc₁)) , tt*
    val≡ : π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ! pq ≡ π γʰ (σ γʰ aʰ bʰ) dʰ ! qq
    val≡ = σπ₀ (γʰ ! (con↓ γʰ kγ)) (aʰ ! (ty↓ aʰ ka)) (bʰ ! (ty↓ bʰ kb)) (dʰ ! (ty↓ dʰ kc)) (conKind γʰ kγ) (tyKind aʰ ka) (getTy₁-kind γʰ aʰ kγ ka ka₁) (tyKind bʰ kb) (getTy₁-kind (▷ γʰ aʰ) bʰ kδ kb kb₁) (tyKind dʰ kc) (getTy₁-kind (▷ (▷ γʰ aʰ) bʰ) dʰ kε kc kc₁)

  ▷-γ : (γ a : CT) → [ ▷ γ a ] ≡ cʰ → [ γ ] ≡ cʰ
  ▷-γ γ a k▷' = mk≡↓ ([]↓ γ γ↓) tt* (▷⁻-kγ γ a ▷↓)
    where
    ▷↓ : ▷ γ a ↓
    ▷↓ = con↓ (▷ γ a) k▷'
    γ↓ : γ ↓
    γ↓ = ▷⁻-γ γ a ▷↓

  ▷-a : (γ a : CT) → [ ▷ γ a ] ≡ cʰ → [ a ] ≡ tʰ
  ▷-a γ a k▷' = mk≡↓ ([]↓ a a↓) tt* (▷⁻-ka γ a ▷↓)
    where
    ▷↓ : ▷ γ a ↓
    ▷↓ = con↓ (▷ γ a) k▷'
    a↓ : a ↓
    a↓ = ▷⁻-a γ a ▷↓

  ▷-a₁ : (γ a : CT) → [ ▷ γ a ] ≡ cʰ → ty₁ a ≡ γ
  ▷-a₁ γ a k▷' = mk≡↓ l↓ r↓ (▷⁻-ka₁ γ a ▷↓)
    where
    ▷↓ : ▷ γ a ↓
    ▷↓ = con↓ (▷ γ a) k▷'
    a↓ : a ↓
    a↓ = ▷⁻-a γ a ▷↓
    γ↓ : γ ↓
    γ↓ = ▷⁻-γ γ a ▷↓
    l↓ : ty₁ a ↓
    l↓ = ∧i a↓ , ∧i ▷⁻-ka γ a ▷↓ , tt*
    r↓ : γ ↓
    r↓ = γ↓

  u-γ : (γ : CT) → [ u γ ] ≡ tʰ → [ γ ] ≡ cʰ
  u-γ γ ku' = mk≡↓ ([]↓ γ γ↓) tt* (u⁻-kγ γ u↓)
    where
    mutual
      [uγ]↓ : [ u γ ] ↓
      [uγ]↓ = transp↓⁻ ku' tt*
      u↓ : u γ ↓
      u↓ = []⁻ (u γ) [uγ]↓
      γ↓ : γ ↓
      γ↓ = u⁻-γ γ u↓

  π-γ : (γ a b : CT) → [ π γ a b ] ≡ tʰ → [ γ ] ≡ cʰ
  π-γ γ a b kπ' = mk≡↓ ([]↓ γ γ↓) tt* (π⁻-kγ γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = transp↓⁻ kπ' tt*
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      γ↓ : γ ↓
      γ↓ = π⁻-γ γ a b π↓

  π-a : (γ a b : CT) → [ π γ a b ] ≡ tʰ → [ a ] ≡ tʰ
  π-a γ a b kπ' = mk≡↓ ([]↓ a a↓) tt* (π⁻-ka γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = transp↓⁻ kπ' tt*
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      a↓ : a ↓
      a↓ = π⁻-a γ a b π↓

  π-a₁ : (γ a b : CT) → [ π γ a b ] ≡ tʰ → ty₁ a ≡ γ
  π-a₁ γ a b kπ' = mk≡↓ l↓ r↓ (π⁻-ka₁ γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = transp↓⁻ kπ' tt*
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      a↓ : a ↓
      a↓ = π⁻-a γ a b π↓
      γ↓ : γ ↓
      γ↓ = π⁻-γ γ a b π↓
      l↓ : ty₁ a ↓
      l↓ = ∧i a↓ , ∧i π⁻-ka γ a b π↓ , tt*
      r↓ : γ ↓
      r↓ = γ↓

  π-b : (γ a b : CT) → [ π γ a b ] ≡ tʰ → [ b ] ≡ tʰ
  π-b γ a b kπ' = mk≡↓ ([]↓ b b↓) tt* (π⁻-kb γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = transp↓⁻ kπ' tt*
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      b↓ : b ↓
      b↓ = π⁻-b γ a b π↓

  π-b₁ : (γ a b : CT) → [ π γ a b ] ≡ tʰ → ty₁ b ≡ ▷ γ a
  π-b₁ γ a b kπ' = mk≡↓ l↓ r↓ (π⁻-kb₁ γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = transp↓⁻ kπ' tt*
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      b↓ : b ↓
      b↓ = π⁻-b γ a b π↓
      δ↓ : ▷ γ a ↓
      δ↓ = ∧i π⁻-γ γ a b π↓ , ∧i π⁻-a γ a b π↓ , ∧i π⁻-kγ γ a b π↓ , ∧i π⁻-ka γ a b π↓ , ∧i π⁻-ka₁ γ a b π↓ , tt*
      l↓ : ty₁ b ↓
      l↓ = ∧i b↓ , ∧i π⁻-kb γ a b π↓ , tt*
      r↓ : ▷ γ a ↓
      r↓ = δ↓

  σ-γ : (γ a b : CT) → [ σ γ a b ] ≡ tʰ → [ γ ] ≡ cʰ
  σ-γ γ a b kσ' = mk≡↓ ([]↓ γ γ↓) tt* (σ⁻-kγ γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = transp↓⁻ kσ' tt*
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      γ↓ : γ ↓
      γ↓ = σ⁻-γ γ a b σ↓

  σ-a : (γ a b : CT) → [ σ γ a b ] ≡ tʰ → [ a ] ≡ tʰ
  σ-a γ a b kσ' = mk≡↓ ([]↓ a a↓) tt* (σ⁻-ka γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = transp↓⁻ kσ' tt*
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      a↓ : a ↓
      a↓ = σ⁻-a γ a b σ↓

  σ-a₁ : (γ a b : CT) → [ σ γ a b ] ≡ tʰ → ty₁ a ≡ γ
  σ-a₁ γ a b kσ' = mk≡↓ l↓ r↓ (σ⁻-ka₁ γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = transp↓⁻ kσ' tt*
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      a↓ : a ↓
      a↓ = σ⁻-a γ a b σ↓
      γ↓ : γ ↓
      γ↓ = σ⁻-γ γ a b σ↓
      l↓ : ty₁ a ↓
      l↓ = ∧i a↓ , ∧i σ⁻-ka γ a b σ↓ , tt*
      r↓ : γ ↓
      r↓ = γ↓

  σ-b : (γ a b : CT) → [ σ γ a b ] ≡ tʰ → [ b ] ≡ tʰ
  σ-b γ a b kσ' = mk≡↓ ([]↓ b b↓) tt* (σ⁻-kb γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = transp↓⁻ kσ' tt*
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      b↓ : b ↓
      b↓ = σ⁻-b γ a b σ↓

  σ-b₁ : (γ a b : CT) → [ σ γ a b ] ≡ tʰ → ty₁ b ≡ ▷ γ a
  σ-b₁ γ a b kσ' = mk≡↓ l↓ r↓ (σ⁻-kb₁ γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = transp↓⁻ kσ' tt*
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      b↓ : b ↓
      b↓ = σ⁻-b γ a b σ↓
      δ↓ : ▷ γ a ↓
      δ↓ = ∧i σ⁻-γ γ a b σ↓ , ∧i σ⁻-a γ a b σ↓ , ∧i σ⁻-kγ γ a b σ↓ , ∧i σ⁻-ka γ a b σ↓ , ∧i σ⁻-ka₁ γ a b σ↓ , tt*
      l↓ : ty₁ b ↓
      l↓ = ∧i b↓ , ∧i σ⁻-kb γ a b σ↓ , tt*
      r↓ : ▷ γ a ↓
      r↓ = δ↓

  wa : W.Algebra (lsuc ℓA)
  wa = record
    { CT = CT
    ; [_] = [_]
    ; ĉ = cʰ
    ; t̂ = tʰ
    ; ty₁ = ty₁
    ; kty₁ = kty₁
    ; ∙ = ∙
    ; k∙ = k∙
    ; ▷ = ▷
    ; k▷ = k▷
    ; ▷-γ = ▷-γ
    ; ▷-a = ▷-a
    ; ▷-a₁ = ▷-a₁
    ; u = u
    ; ku = ku
    ; u₁ = u₁
    ; u-γ = u-γ
    ; π = π
    ; kπ = kπ
    ; π₁ = π₁
    ; π-γ = π-γ
    ; π-a = π-a
    ; π-a₁ = π-a₁
    ; π-b = π-b
    ; π-b₁ = π-b₁
    ; σ = σ
    ; kσ = kσ
    ; σ₁ = σ₁
    ; σ-γ = σ-γ
    ; σ-a = σ-a
    ; σ-a₁ = σ-a₁
    ; σ-b = σ-b
    ; σ-b₁ = σ-b₁
    ; σ▷ = σ▷
    ; σπ = σπ
    }

{- 

G₁ : ∀ {ℓA} {A B : M.Algebra ℓA} → M.Hom A B → W.Hom (G₀ A) (G₀ B)
G₁ {ℓA} {A} {B} f = record
  { θ = θ
  ; [_] = [_]
  ; ĉ = ≡.refl
  ; t̂ = t̂
  ; ty₁ = ty₁
  ; ∙ = ∙
  ; ▷ = ▷
  ; u = u
  ; π = π
  ; σ = σ
  }
  module G₁ where
  module A = M.Algebra A
  module B = M.Algebra B
  module GA = G₀ A
  module GB = G₀ B
  module f = M.Hom f

  θ₀ : GA.Atom → GB.Atom
  θ₀ (GA.con γ) = GB.con (f.conᴿ γ)
  θ₀ (GA.ty a) = GB.ty (f.tyᴿ a)
  θ₀ (GA.k̂) = GB.k̂
  θ₀ (GA.ĉ) = GB.ĉ
  θ₀ GA.t̂ = GB.t̂

  θ : GA.CT → GB.CT
  θ (P ⊢ x) = P ⊢ λ p → θ₀ (x p)

  [_]₀ : ∀ x → θ₀ (GA.[ x ]₀) ≡ GB.[ θ₀ x ]₀
  [ GA.con x ]₀ = ≡.refl
  [ GA.ty γ a ]₀ = ≡.refl
  [ GA.k̂ ]₀ = ≡.refl
  [ GA.ĉ ]₀ = ≡.refl
  [ GA.t̂ ]₀ = ≡.refl

  [_] : ∀ (x : GA.CT) → θ (GA.[ x ]) ≡ GB.[ θ x ]
  [ P ⊢ x ] = GB.mkCT≡ (λ p → p) (λ p → p) λ p q → [ x (p .∧e₂) ]₀

  ty₁₀ : ∀ a → θ₀ (GA.ty₁₀ a) ≡ GB.ty₁₀ (θ₀ a)
  ty₁₀ (GA.ty a) = ≡.cong GB.con (f.ty₁ᴿ a)

  θ-kc : (γ : GA.Atom) → GA.[ γ ]₀ ≡ GA.ĉ → GB.[ θ₀ γ ]₀ ≡ GB.ĉ
  θ-kc γ kγ = ≡.trans (≡.sym [ γ ]₀) (≡.cong θ₀ kγ)

  θ-ka : (a : GA.Atom) → GA.[ a ]₀ ≡ GA.t̂ → GB.[ θ₀ a ]₀ ≡ GB.t̂
  θ-ka a ka = ≡.trans (≡.sym [ a ]₀) (≡.cong θ₀ ka)

  θ-ka₁ : (γ a : GA.Atom)
    → (kγ : GA.[ γ ]₀ ≡ GA.ĉ)
    → (ka : GA.[ a ]₀ ≡ GA.t̂)
    → GA.ty₁₀ a ka ≡ γ
    → GB.ty₁₀ (θ₀ a) (θ-ka a ka) ≡ θ₀ γ
  θ-ka₁ γ a kγ ka ka₁ = trans (sym (ty₁₀ a)) (trans (≡.cong θ₀ ka₁) (ty₁₀ γ))

  θ-▷₀ : (γ a : GA.Atom)
    → (kγ : GA.[ γ ]₀ ≡ GA.ĉ)
    → (ka : GA.[ a ]₀ ≡ GA.t̂)
    → (ka₁ : GA.ty₁₀ a ka ≡ γ)
    → θ₀ (GA.▷₀ γ a kγ ka ka₁)
    ≡ GB.▷₀ (θ₀ γ) (θ₀ a) (θ-kc γ kγ) (θ-ka a ka) (θ-ka₁ γ a kγ ka ka₁)
  θ-▷₀ (GA.con γ) (GA.ty a) ≡.refl ≡.refl ka₁ = ≡.cong GB.con (f.▷ᴿ γ a (GA.con-inj ka₁) (GB.con-inj (θ-ka₁ _ _ _ _ ka₁)))

  θ-kb : (b : GA.Atom) → GA.[ b ]₀ ≡ GA.t̂ → GB.[ θ₀ b ]₀ ≡ GB.t̂
  θ-kb b kb = ≡.trans (≡.sym [ b ]₀) (≡.cong θ₀ kb)

  θ-kb₁ : (γ a b : GA.Atom)
    → (kγ : GA.[ γ ]₀ ≡ GA.ĉ)
    → (ka : GA.[ a ]₀ ≡ GA.t̂)
    → (ka₁ : GA.ty₁₀ a ka ≡ γ)
    → (kb : GA.[ b ]₀ ≡ GA.t̂)
    → GA.ty₁₀ b kb ≡ GA.▷₀ γ a kγ ka ka₁
    → GB.ty₁₀ (θ₀ b) (θ-kb b kb)
      ≡ GB.▷₀ (θ₀ γ) (θ₀ a) (θ-kc γ kγ) (θ-ka a ka) (θ-ka₁ γ a kγ ka ka₁)
  θ-kb₁ γ a b kγ ka ka₁ kb kb₁ = trans (sym (ty₁₀ b)) (trans (≡.cong θ₀ kb₁) (θ-▷₀ γ a kγ ka ka₁))

  θ-u₀ : (γ : GA.Atom) (kγ : GA.[ γ ]₀ ≡ GA.ĉ)
    → θ₀ (GA.u₀ γ kγ) ≡ GB.u₀ (θ₀ γ) (θ-kc γ kγ)
  θ-u₀ (GA.con γ) ≡.refl = ≡.cong GB.ty (f.uᴿ γ)

  θ-π₀ : (γ a b : GA.Atom) (kγ : GA.[ γ ]₀ ≡ GA.ĉ) (ka : GA.[ a ]₀ ≡ GA.t̂ γ)
    (kb : GA.[ b ]₀ ≡ GA.t̂ (GA.▷₀ γ a kγ ka))
    → θ₀ (GA.π₀ γ a b kγ ka kb)
    ≡ GB.π₀ (θ₀ γ) (θ₀ a) (θ₀ b) (θ-kc γ kγ) (θ-ka γ a ka) (θ-kb γ a b kγ ka kb)
  θ-π₀ (GA.con γ) (GA.ty .γ a) (GA.ty .(γ A.▷ a) b) ≡.refl ≡.refl ≡.refl =
    ≡.cong (GB.ty (f.conᴿ γ)) (f.πᴿ γ a b)

  θ-σ₀ : (γ a b : GA.Atom) (kγ : GA.[ γ ]₀ ≡ GA.ĉ) (ka : GA.[ a ]₀ ≡ GA.t̂ γ)
    (kb : GA.[ b ]₀ ≡ GA.t̂ (GA.▷₀ γ a kγ ka))
    → θ₀ (GA.σ₀ γ a b kγ ka kb)
    ≡ GB.σ₀ (θ₀ γ) (θ₀ a) (θ₀ b) (θ-kc γ kγ) (θ-ka γ a ka) (θ-kb γ a b kγ ka kb)
  θ-σ₀ (GA.con γ) (GA.ty .γ a) (GA.ty .(γ A.▷ a) b) ≡.refl ≡.refl ≡.refl =
    ≡.cong (GB.ty (f.conᴿ γ)) (f.σᴿ γ a b)

  t̂ : ∀ γ → θ (GA.tʰ γ) ≡ GB.tʰ (θ γ)
  t̂ (P ⊢ x) = GB.mkCT≡ (λ p → p) (λ p → p) λ p q → ≡.refl

  ∙ : θ GA.∙ ≡ GB.∙
  ∙ = mk≡↓ (liftp tt) (liftp tt) (≡.cong GB.con f.∙ᴿ)

  ▷ : ∀ (γ : GA.CT) (a : GA.CT)
    → GA.[ γ ] ≡ GA.cʰ
    → GA.[ a ] ≡ GA.tʰ γ
    → θ (GA.▷ γ a) ≡ GB.▷ (θ γ) (θ a)
  ▷ γʰ aʰ kγ ka = mk≡↓ pq qq val≡
    where
    qq : (GB.▷ (θ γʰ) (θ aʰ)) ↓
    qq = ∧i GA.con↓ γʰ kγ ,
         ∧i GA.ty↓ γʰ aʰ kγ ka ,
         ∧i θ-kc (γʰ ! (GA.con↓ γʰ kγ)) (GA.conKind γʰ kγ) ,
         ∧i θ-ka (γʰ ! (GA.con↓ γʰ kγ)) (aʰ ! (GA.ty↓ γʰ aʰ kγ ka)) (GA.tyKind γʰ aʰ kγ ka) ,
         liftp tt
    q : (GB.▷ (θ γʰ) (θ aʰ)) ↓ → (θ (GA.▷ γʰ aʰ)) ↓
    q _ = ∧i GA.con↓ γʰ kγ ,
          ∧i GA.ty↓ γʰ aʰ kγ ka ,
          ∧i GA.conKind γʰ kγ ,
          ∧i GA.tyKind γʰ aʰ kγ ka ,
          liftp tt
    pq : (θ (GA.▷ γʰ aʰ)) ↓
    pq = q qq
    val≡ : θ (GA.▷ γʰ aʰ) ! pq ≡ GB.▷ (θ γʰ) (θ aʰ) ! qq
    val≡ = θ-▷₀ (γʰ ! (GA.con↓ γʰ kγ)) (aʰ ! (GA.ty↓ γʰ aʰ kγ ka)) (GA.conKind γʰ kγ) (GA.tyKind γʰ aʰ kγ ka)

  u : ∀ (γ : GA.CT) → GA.[ γ ] ≡ GA.cʰ → θ (GA.u γ) ≡ GB.u (θ γ)
  u γʰ kγ = mk≡↓ pq qq val≡
    where
    qq : (GB.u (θ γʰ)) ↓
    qq = ∧i GA.con↓ γʰ kγ , ∧i θ-kc (γʰ ! (GA.con↓ γʰ kγ)) (GA.conKind γʰ kγ) , liftp tt
    q : (GB.u (θ γʰ)) ↓ → (θ (GA.u γʰ)) ↓
    q _ = ∧i GA.con↓ γʰ kγ , ∧i GA.conKind γʰ kγ , liftp tt
    pq : (θ (GA.u γʰ)) ↓
    pq = q qq
    val≡ : θ (GA.u γʰ) ! pq ≡ GB.u (θ γʰ) ! qq
    val≡ = θ-u₀ (γʰ ! (GA.con↓ γʰ kγ)) (GA.conKind γʰ kγ)

  π : ∀ (γ : GA.CT) (a : GA.CT) (b : GA.CT)
    → GA.[ γ ] ≡ GA.cʰ
    → GA.[ a ] ≡ GA.tʰ γ
    → GA.[ b ] ≡ GA.tʰ (GA.▷ γ a)
    → θ (GA.π γ a b) ≡ GB.π (θ γ) (θ a) (θ b)
  π γʰ aʰ bʰ kγ ka kb = mk≡↓ pq qq val≡
    where
    kδ = GA.k▷ γʰ aʰ kγ ka
    qq : (GB.π (θ γʰ) (θ aʰ) (θ bʰ)) ↓
    qq = ∧i GA.con↓ γʰ kγ ,
         ∧i GA.ty↓ γʰ aʰ kγ ka ,
         ∧i GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb ,
         ∧i θ-kc (γʰ ! (GA.con↓ γʰ kγ))
                 (GA.conKind γʰ kγ) ,
         ∧i θ-ka (γʰ ! (GA.con↓ γʰ kγ))
                 (aʰ ! (GA.ty↓ γʰ aʰ kγ ka))
                 (GA.tyKind γʰ aʰ kγ ka) ,
         ∧i θ-kb (γʰ ! (GA.con↓ γʰ kγ))
                 (aʰ ! (GA.ty↓ γʰ aʰ kγ ka))
                 (bʰ ! (GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb))
                 (GA.conKind γʰ kγ)
                 (GA.tyKind γʰ aʰ kγ ka)
                 (GA.getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb) ,
         liftp tt
    q : (GB.π (θ γʰ) (θ aʰ) (θ bʰ)) ↓ → (θ (GA.π γʰ aʰ bʰ)) ↓
    q _ = ∧i GA.con↓ γʰ kγ ,
          ∧i GA.ty↓ γʰ aʰ kγ ka ,
          ∧i GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i GA.conKind γʰ kγ ,
          ∧i GA.tyKind γʰ aʰ kγ ka ,
          ∧i GA.getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb ,
          liftp tt
    pq : (θ (GA.π γʰ aʰ bʰ)) ↓
    pq = q qq
    val≡ : θ (GA.π γʰ aʰ bʰ) ! pq ≡ GB.π (θ γʰ) (θ aʰ) (θ bʰ) ! qq
    val≡ = θ-π₀ (γʰ ! (GA.con↓ γʰ kγ))
                (aʰ ! (GA.ty↓ γʰ aʰ kγ ka))
                (bʰ ! (GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb))
                (GA.conKind γʰ kγ)
                (GA.tyKind γʰ aʰ kγ ka)
                (GA.getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb)

  σ : ∀ (γ : GA.CT) (a : GA.CT) (b : GA.CT)
    → GA.[ γ ] ≡ GA.cʰ
    → GA.[ a ] ≡ GA.tʰ γ
    → GA.[ b ] ≡ GA.tʰ (GA.▷ γ a)
    → θ (GA.σ γ a b) ≡ GB.σ (θ γ) (θ a) (θ b)
  σ γʰ aʰ bʰ kγ ka kb = mk≡↓ pq qq val≡
    where
    kδ = GA.k▷ γʰ aʰ kγ ka
    qq : (GB.σ (θ γʰ) (θ aʰ) (θ bʰ)) ↓
    qq = ∧i GA.con↓ γʰ kγ ,
         ∧i GA.ty↓ γʰ aʰ kγ ka ,
         ∧i GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb ,
         ∧i θ-kc (γʰ ! (GA.con↓ γʰ kγ)) (GA.conKind γʰ kγ) ,
         ∧i θ-ka (γʰ ! (GA.con↓ γʰ kγ)) (aʰ ! (GA.ty↓ γʰ aʰ kγ ka)) (GA.tyKind γʰ aʰ kγ ka) ,
         ∧i θ-kb (γʰ ! (GA.con↓ γʰ kγ)) (aʰ ! (GA.ty↓ γʰ aʰ kγ ka)) (bʰ ! (GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb)) (GA.conKind γʰ kγ) (GA.tyKind γʰ aʰ kγ ka) (GA.getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb) ,
         liftp tt
    q : (GB.σ (θ γʰ) (θ aʰ) (θ bʰ)) ↓ → (θ (GA.σ γʰ aʰ bʰ)) ↓
    q _ = ∧i GA.con↓ γʰ kγ ,
          ∧i GA.ty↓ γʰ aʰ kγ ka ,
          ∧i GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i GA.conKind γʰ kγ ,
          ∧i GA.tyKind γʰ aʰ kγ ka ,
          ∧i GA.getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb ,
          liftp tt
    pq : (θ (GA.σ γʰ aʰ bʰ)) ↓
    pq = q qq
    val≡ : θ (GA.σ γʰ aʰ bʰ) ! pq ≡ GB.σ (θ γʰ) (θ aʰ) (θ bʰ) ! qq
    val≡ = θ-σ₀ (γʰ ! (GA.con↓ γʰ kγ)) (aʰ ! (GA.ty↓ γʰ aʰ kγ ka)) (bʰ ! (GA.ty▷↓ γʰ aʰ bʰ kγ ka kδ kb)) (GA.conKind γʰ kγ) (GA.tyKind γʰ aʰ kγ ka) (GA.getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb)

G : ∀ {ℓA} → Functor (M.Cat ℓA) (W.Cat (lsuc ℓA))
G = record
  { ob = G₀
  ; hom = G₁
  ; id = id
  ; comp = comp
  ; resp = resp
  }
  where
  id-θ₀ : ∀ {ℓA} {A : M.Algebra ℓA} (x : G₀.Atom A) → G₁.θ₀ (M.id {A = A}) x ≡ x
  id-θ₀ (G₀.con _) = ≡.refl
  id-θ₀ (G₀.ty _ _) = ≡.refl
  id-θ₀ G₀.k̂ = ≡.refl
  id-θ₀ G₀.ĉ = ≡.refl
  id-θ₀ (G₀.t̂ x) = ≡.cong G₀.t̂ (id-θ₀ x)

  id : ∀ {ℓA} {A : M.Algebra ℓA} → G₁ (M.id {A = A}) W.≈ W.id {A = G₀ A}
  id {ℓA} {A} = W.mk≈ λ { (P ⊢ x) → G₀.mkCT≡ A (λ p → p) (λ p → p) (λ p q → id-θ₀ (x p)) }

  comp-θ₀ : ∀ {ℓA} {A B C : M.Algebra ℓA} (f : M.Hom A B) (g : M.Hom B C) (x : G₀.Atom A)
    → G₁.θ₀ (g M.∘ f) x ≡ G₁.θ₀ g (G₁.θ₀ f x)
  comp-θ₀ f g (G₀.con _) = ≡.refl
  comp-θ₀ f g (G₀.ty _ _) = ≡.refl
  comp-θ₀ f g G₀.k̂ = ≡.refl
  comp-θ₀ f g G₀.ĉ = ≡.refl
  comp-θ₀ f g (G₀.t̂ x) = ≡.cong G₀.t̂ (comp-θ₀ f g x)

  comp : ∀ {ℓA} {A B C : M.Algebra ℓA} (f : M.Hom A B) (g : M.Hom B C)
    → G₁ (g M.∘ f) W.≈ (G₁ g W.∘ G₁ f)
  comp {ℓA} {A} {B} {C} f g = W.mk≈ λ { (P ⊢ x) → G₀.mkCT≡ C (λ p → p) (λ p → p) λ p q → comp-θ₀ f g (x p) }

  resp-θ₀ : ∀ {ℓA} {A B : M.Algebra ℓA} {f g : M.Hom A B} → f M.≈ g → (x : G₀.Atom A)
    → G₁.θ₀ f x ≡ G₁.θ₀ g x
  resp-θ₀ {f = f} {g} p (G₀.con γ) = ≡.cong G₀.con (p .M.con≡ γ)
  resp-θ₀ {f = f} {g} p (G₀.ty γ a) = ≡.dcong₂ G₀.ty (p .M.con≡ γ) (p .M.ty≡ γ a)
  resp-θ₀ p G₀.k̂ = ≡.refl
  resp-θ₀ p G₀.ĉ = ≡.refl
  resp-θ₀ p (G₀.t̂ x) = ≡.cong G₀.t̂ (resp-θ₀ p x)

  resp : ∀ {ℓA} {A B : M.Algebra ℓA} {f g : M.Hom A B} → f M.≈ g → G₁ f W.≈ G₁ g
  resp {ℓA} {A} {B} {f} {g} p = W.mk≈ λ { (P ⊢ x) → G₀.mkCT≡ B (λ q → q) (λ q → q) (λ q r → resp-θ₀ p (x q)) }

-}
