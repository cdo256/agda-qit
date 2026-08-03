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
G₀ {ℓA} da = {!wa!}
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

  -- [kʰ]≢cʰ : [ kʰ ] ≢ cʰ
  -- [kʰ]≢cʰ p =
  --   let x , q = map-return-inj [_]₀ kʰ ĉ p
  --   in ⊥e* (encode q)

  -- [kʰ]≢tʰ : ∀ {x*} → [ kʰ ] ≢ tʰ
  -- [kʰ]≢tʰ {x*} p = ⊥e* (encode (u .snd))
  --   where
  --   u : ΣP Atom (λ x → t̂ x ≡ [ k̂ ]₀)
  --   u = map-return-inj t̂ x* [ k̂ ]₀ (sym (≡.trans (sym (map-beta [_]₀ k̂)) p))

  -- [cʰ]≢cʰ : [ cʰ ] ≢ cʰ
  -- [cʰ]≢cʰ p =
  --   let x , q = map-return-inj [_]₀ kʰ ĉ p
  --   in ⊥e* (encode q)

  -- [cʰ]≢tʰ : ∀ {x*} → [ cʰ ] ≢ tʰ x*
  -- [cʰ]≢tʰ {x*} p = ⊥e* (encode (u .snd))
  --   where
  --   u : ΣP Atom (λ x → t̂ x ≡ [ ĉ ]₀)
  --   u = map-return-inj t̂ x* [ ĉ ]₀ (sym (≡.trans (sym (map-beta [_]₀ ĉ)) p))

  -- [tʰ]≢cʰ : ∀ {x*} → [ tʰ x* ] ≢ cʰ
  -- [tʰ]≢cʰ {x*} p = q (≡.trans (≡.sym (map-fold [_]₀ t̂ x*)) p)
  --   where
  --   q : map ([_]₀ ∘ t̂) x* ≢ return ĉ
  --   q = map≢return ([_]₀ ∘ t̂) x* ĉ λ x ()

  -- [tʰ]≢tʰ : ∀ {x* y*} → x* ↓ → [ tʰ x* ] ≢ tʰ y*
  -- [tʰ]≢tʰ {x*} {y*} x↓ p = map≢map ([_]₀ ∘ t̂) t̂ x* y* x↓ (λ _ _ ()) q
  --   where
  --   q : map ([_]₀ ∘ t̂) x* ≡ map t̂ y*
  --   q = trans (sym (map-fold [_]₀ t̂ x*)) p

  -- [[x]]≢cʰ : ∀ {x*} → [ [ x* ] ] ≢ cʰ
  -- [[x]]≢cʰ {x*} p =
  --   map≢return
  --     ([_]₀ ∘ [_]₀) x* ĉ
  --     (λ x q → k̂≢ĉ (trans (sym ([[x]]₀≡k̂ x)) q))
  --     (trans (sym (map-fold [_]₀ [_]₀ x*)) p)

  -- [[x]]≢tʰ : ∀ {x* y*} → x* ↓ → [ [ x* ] ] ≢ tʰ y*
  -- [[x]]≢tʰ {x*} {y*} x↓ p =
  --   map≢map
  --     ([_]₀ ∘ [_]₀) t̂ x* y* x↓
  --     (λ x y q → k̂≢t̂ (trans (sym ([[x]]₀≡k̂ x)) q))
  --     (trans (sym (map-fold [_]₀ [_]₀ x*)) p)

  -- [[x]]≡kʰ : ∀ x* → x* ↓ → [ [ x* ] ] ≡ kʰ
  -- [[x]]≡kʰ x* x↓ =
  --   mk≡↓ (∧i tt* , ∧i tt* , x↓) tt* ([[x]]₀≡k̂ x)
  --   where
  --   x : Atom
  --   x = x* ! x↓

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
  k▷₀ (con γ) (ty a) refl refl a₁ = refl

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
  Con₀-▷₀ (con γ) (ty a) refl refl a₁ = refl

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
  σ▷₀ (con γ) (ty a) (ty b) refl refl a₁ refl b₁ =
    cong con
      (MA.σ▷ (Con₀ (con γ) refl)
             (Ty₀ (ty a) refl)
             (Ty₀ (ty b) refl)
             (Ty₀₁ (con γ) (ty a) refl refl a₁)
             (trans (Ty₀₁ (▷₀ (con γ) (ty a) refl refl a₁) (ty b) (k▷₀ (con γ) (ty a) refl refl a₁) refl b₁)
                    (Con₀-▷₀ (con γ) (ty a) refl refl a₁)))

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
  σπ₀ (con γ) (ty a) (ty b) (ty d) refl refl a₁ refl b₁ refl d₁ =
    cong ty
      (MA.σπ (Con₀ (con γ) refl)
             (Ty₀ (ty a) refl)
             (Ty₀ (ty b) refl)
             (Ty₀ (ty d) refl)
             (Ty₀₁ (con γ) (ty a) refl refl a₁)
             (trans (Ty₀₁ (▷₀ (con γ) (ty a) refl refl a₁) (ty b) (k▷₀ (con γ) (ty a) refl refl a₁) refl b₁)
                    (Con₀-▷₀ (con γ) (ty a) refl refl a₁))
             (Ty₀₁ (▷₀ (▷₀ (con γ) (ty a) refl refl a₁) (ty b) (k▷₀ (con γ) (ty a) refl refl a₁) refl b₁) (ty d)
                   (k▷₀ (▷₀ (con γ) (ty a) refl refl a₁) (ty b) (k▷₀ (con γ) (ty a) refl refl a₁) refl b₁) refl d₁))

  con↓ : (γʰ : CT) → [ γʰ ] ≡ cʰ → γʰ ↓
  con↓ γʰ kγ = extractCond kγ tt* .∧e₂

  getConAtom : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → Atom
  getConAtom γʰ kγ = γʰ ! (con↓ γʰ kγ)

  conKind : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → [ getConAtom γʰ kγ ]₀ ≡ ĉ
  conKind γʰ kγ = extractVal kγ tt*

  getConΣ : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → ConΣ
  getConΣ γʰ kγ = getConAtom γʰ kγ , conKind γʰ kγ

  getCon : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → MA.Con
  getCon γʰ kγ = ConΣ→Con (getConΣ γʰ kγ)

  ty↓ : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → aʰ ↓
  ty↓ aʰ ka = extractCond ka tt* .∧e₂

  []↓ : ∀ x → x ↓ → [ x ] ↓
  []↓ x x↓ = ∧i tt* , x↓

  getTyAtom : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → Atom
  getTyAtom aʰ ka = aʰ ! (ty↓ aʰ ka)

  tyKind : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → [ getTyAtom aʰ ka ]₀ ≡ t̂
  tyKind aʰ ka = extractVal ka tt*

  ty₁↓ : (aʰ : CT) → (ka : [ aʰ ] ≡ tʰ) → ty₁ aʰ ↓
  ty₁↓ aʰ ka = ∧i ty↓ aʰ ka , ∧i tyKind aʰ ka , tt*

  getTy₁-kind : (γʰ aʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ)
    → (ka₁ : ty₁ aʰ ≡ γʰ)
    → ty₁₀ (getTyAtom aʰ ka) (tyKind aʰ ka) ≡ getConAtom γʰ kγ
  getTy₁-kind γʰ aʰ kγ ka ka₁ = extractVal ka₁ (con↓ γʰ kγ)

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
    l↓ = ∧i (∧i con↓ γʰ kγ , ∧i conKind γʰ kγ , tt*) , ∧i extractVal (ku γʰ kγ) tt* , tt*
    r↓ : γʰ ↓
    r↓ = con↓ γʰ kγ
    val≡ : ty₁ (u γʰ) ! l↓ ≡ γʰ ! r↓
    val≡ = u₁₀ (γʰ ! r↓) (conKind γʰ kγ)

{- 

  π : CT → CT → CT → CT
  π γʰ aʰ bʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    bʰ >>= λ b →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂ γ) λ ka →
    assume ([ b ]₀ ≡ t̂ (▷₀ γ a kγ ka)) λ kb →
    return (ty (Con₀ γ kγ)
               (MA.π (Con₀ γ kγ)
                     (Ty₀ γ a kγ ka)
                     (Ty₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb)))

  π⁻-γ : ∀ γʰ aʰ bʰ
    → π γʰ aʰ bʰ ↓
    → γʰ ↓
  π⁻-γ γʰ aʰ bʰ π↓ = π↓ .∧e₁
  π⁻-a : ∀ γʰ aʰ bʰ
    → π γʰ aʰ bʰ ↓
    → aʰ ↓
  π⁻-a γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₁
  π⁻-b : ∀ γʰ aʰ bʰ
    → π γʰ aʰ bʰ ↓
    → bʰ ↓
  π⁻-b γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₁
  π⁻-kγ : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → [ γʰ ! (π⁻-γ γʰ aʰ bʰ π↓) ]₀ ≡ ĉ
  π⁻-kγ γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₁
  π⁻-ka : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → [ aʰ ! (π⁻-a γʰ aʰ bʰ π↓) ]₀ ≡ t̂ (γʰ ! (π⁻-γ γʰ aʰ bʰ π↓))
  π⁻-ka γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁
  π⁻-kb : ∀ γʰ aʰ bʰ
    → (π↓ : π γʰ aʰ bʰ ↓)
    → [ bʰ ! (π⁻-b γʰ aʰ bʰ π↓) ]₀
    ≡ t̂ (▷₀ (γʰ ! (π⁻-γ γʰ aʰ bʰ π↓))
             (aʰ ! (π⁻-a γʰ aʰ bʰ π↓))
             (π⁻-kγ γʰ aʰ bʰ π↓)
             (π⁻-ka γʰ aʰ bʰ π↓))
  π⁻-kb γʰ aʰ bʰ π↓ = π↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  σ : CT → CT → CT → CT
  σ γʰ aʰ bʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    bʰ >>= λ b →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂ γ) λ ka →
    assume ([ b ]₀ ≡ t̂ (▷₀ γ a kγ ka)) λ kb →
    return (σ₀ γ a b kγ ka kb)

  σ⁻-γ : ∀ γʰ aʰ bʰ
    → σ γʰ aʰ bʰ ↓
    → γʰ ↓
  σ⁻-γ γʰ aʰ bʰ σ↓ = σ↓ .∧e₁
  σ⁻-a : ∀ γʰ aʰ bʰ
    → σ γʰ aʰ bʰ ↓
    → aʰ ↓
  σ⁻-a γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₁
  σ⁻-b : ∀ γʰ aʰ bʰ
    → σ γʰ aʰ bʰ ↓
    → bʰ ↓
  σ⁻-b γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₁
  σ⁻-kγ : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → [ γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓) ]₀ ≡ ĉ
  σ⁻-kγ γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₁
  σ⁻-ka : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → [ aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓) ]₀ ≡ t̂ (γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓))
  σ⁻-ka γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁
  σ⁻-kb : ∀ γʰ aʰ bʰ
    → (σ↓ : σ γʰ aʰ bʰ ↓)
    → [ bʰ ! (σ⁻-b γʰ aʰ bʰ σ↓) ]₀
    ≡ t̂ (▷₀ (γʰ ! (σ⁻-γ γʰ aʰ bʰ σ↓))
             (aʰ ! (σ⁻-a γʰ aʰ bʰ σ↓))
             (σ⁻-kγ γʰ aʰ bʰ σ↓)
             (σ⁻-ka γʰ aʰ bʰ σ↓))
  σ⁻-kb γʰ aʰ bʰ σ↓ = σ↓ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  ty▷↓ : (γʰ aʰ bʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → (kδ : [ ▷ γʰ aʰ ] ≡ cʰ)
    → (kb : [ bʰ ] ≡ tʰ (▷ γʰ aʰ))
    → bʰ ↓
  ty▷↓ γʰ aʰ bʰ kγ ka kδ kb = extractCond kb (∧i tt* , con↓ (▷ γʰ aʰ) kδ) .∧e₂

  getTy▷-kind : (γʰ aʰ bʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → (kδ : [ ▷ γʰ aʰ ] ≡ cʰ)
    → (kb : [ bʰ ] ≡ tʰ (▷ γʰ aʰ))
    → [ bʰ ! (ty▷↓ γʰ aʰ bʰ kγ ka kδ kb) ]₀
    ≡ t̂ (▷₀ (γʰ ! (con↓ γʰ kγ))
             (aʰ ! (ty↓ γʰ aʰ kγ ka))
             (conKind γʰ kγ)
             (tyKind γʰ aʰ kγ ka))
  getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb = tyKind (▷ γʰ aʰ) bʰ kδ kb

  kk̂ : [ kʰ ] ≡ kʰ
  kk̂ = mk≡↓ (∧i tt* , tt*) tt* refl

  kĉ : [ cʰ ] ≡ kʰ
  kĉ = mk≡↓ (∧i tt* , tt*) tt* refl

  kt̂ : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ tʰ γʰ ] ≡ kʰ
  kt̂ γʰ kγ = mk≡↓ (∧i tt* , ∧i tt* , con↓ γʰ kγ) tt* refl

  k∙ : [ ∙ ] ≡ cʰ
  k∙ = mk≡↓ (∧i tt* , tt*) tt* refl

  k▷ : (γʰ aʰ : CT) → [ γʰ ] ≡ cʰ → [ aʰ ] ≡ tʰ γʰ → [ ▷ γʰ aʰ ] ≡ cʰ
  k▷ γʰ aʰ kγ ka = mk≡↓ q tt* refl
    module k▷ where
    q : [ ▷ γʰ aʰ ] ↓
    q = ∧i tt* ,
        ∧i con↓ γʰ kγ ,
        ∧i ty↓ γʰ aʰ kγ ka ,
        ∧i conKind γʰ kγ ,
        ∧i tyKind γʰ aʰ kγ ka ,
        tt*

  ku : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ u γʰ ] ≡ tʰ γʰ
  ku γʰ kγ = mk≡↓ l↓ r↓ val≡
    module ku where
    l↓ : [ u γʰ ] ↓
    l↓ = ∧i tt* , ∧i con↓ γʰ kγ , ∧i conKind γʰ kγ , tt*
    r↓ : tʰ γʰ ↓
    r↓ = ∧i tt* , con↓ γʰ kγ
    val≡ : [ u γʰ ] ! l↓ ≡ tʰ γʰ ! r↓
    val≡ =
      [ u γʰ ] ! l↓
        ≡⟨ ku₀ (γʰ ! (con↓ γʰ kγ)) (conKind γʰ kγ) ⟩
      t̂ (γʰ ! (con↓ γʰ kγ))
        ≡⟨ refl ⟩
      tʰ γʰ ! r↓ ∎

  kπ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → [ π γʰ aʰ bʰ ] ≡ tʰ γʰ
  kπ γʰ aʰ bʰ kγ ka kb = mk≡↓ pq tq val≡
    module kπ where
    kδ = k▷ γʰ aʰ kγ ka
    tq : tʰ γʰ ↓
    tq = ∧i tt* , con↓ γʰ kγ
    q : tʰ γʰ ↓ → [ π γʰ aʰ bʰ ] ↓
    q _ = ∧i tt* ,
          ∧i con↓ γʰ kγ ,
          ∧i ty↓ γʰ aʰ kγ ka ,
          ∧i ty▷↓ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i conKind γʰ kγ ,
          ∧i tyKind γʰ aʰ kγ ka ,
          ∧i getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb ,
          tt*
    pq : [ π γʰ aʰ bʰ ] ↓
    pq = q tq
    val≡ : [ π γʰ aʰ bʰ ] ! pq ≡ tʰ γʰ ! tq
    val≡ =
      trans (kπ₀ (γʰ ! (con↓ γʰ kγ))
                  (aʰ ! (ty↓ γʰ aʰ kγ ka))
                  (bʰ ! (ty▷↓ γʰ aʰ bʰ kγ ka kδ kb))
                  (conKind γʰ kγ)
                  (tyKind γʰ aʰ kγ ka)
                  (getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb))
            (cong t̂ (congp (γʰ .val)))

  kσ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → [ σ γʰ aʰ bʰ ] ≡ tʰ γʰ
  kσ γʰ aʰ bʰ kγ ka kb = mk≡↓ pq tq val≡
    module kσ where
    kδ = k▷ γʰ aʰ kγ ka
    tq : tʰ γʰ ↓
    tq = ∧i tt* , con↓ γʰ kγ
    q : tʰ γʰ ↓ → [ σ γʰ aʰ bʰ ] ↓
    q _ = ∧i tt* ,
          ∧i con↓ γʰ kγ ,
          ∧i ty↓ γʰ aʰ kγ ka ,
          ∧i ty▷↓ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i conKind γʰ kγ ,
          ∧i tyKind γʰ aʰ kγ ka ,
          ∧i getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb ,
          tt*
    pq : [ σ γʰ aʰ bʰ ] ↓
    pq = q tq
    val≡ : [ σ γʰ aʰ bʰ ] ! pq ≡ tʰ γʰ ! tq
    val≡ =
      trans (kσ₀ (γʰ ! (con↓ γʰ kγ))
                  (aʰ ! (ty↓ γʰ aʰ kγ ka))
                  (bʰ ! (ty▷↓ γʰ aʰ bʰ kγ ka kδ kb))
                  (conKind γʰ kγ)
                  (tyKind γʰ aʰ kγ ka)
                  (getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb))
            (cong t̂ (congp (γʰ .val)))

  σ▷ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → ▷ (▷ γʰ aʰ) bʰ ≡ ▷ γʰ (σ γʰ aʰ bʰ)
  σ▷ γʰ aʰ bʰ kγ ka kb = mk≡↓ pq qq val≡
    module σ▷ where
    kδ = k▷ γʰ aʰ kγ ka
    qq : ▷ γʰ (σ γʰ aʰ bʰ) ↓
    qq = ∧i con↓ γʰ kγ ,
          ∧i ty↓ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          ∧i conKind γʰ kγ ,
          ∧i tyKind γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          tt*
    q : ▷ γʰ (σ γʰ aʰ bʰ) ↓ → ▷ (▷ γʰ aʰ) bʰ ↓
    q _ = ∧i con↓ (▷ γʰ aʰ) kδ ,
          ∧i ty↓ (▷ γʰ aʰ) bʰ kδ kb ,
          ∧i conKind (▷ γʰ aʰ) kδ ,
          ∧i tyKind (▷ γʰ aʰ) bʰ kδ kb ,
          tt*
    pq : ▷ (▷ γʰ aʰ) bʰ ↓
    pq = q qq
    val≡ : ▷ (▷ γʰ aʰ) bʰ ! pq ≡ ▷ γʰ (σ γʰ aʰ bʰ) ! qq
    val≡ =
      σ▷₀ (γʰ ! (con↓ γʰ kγ))
          (aʰ ! (ty↓ γʰ aʰ kγ ka))
          (bʰ ! (ty▷↓ γʰ aʰ bʰ kγ ka kδ kb))
          (conKind γʰ kγ)
          (tyKind γʰ aʰ kγ ka)
          (getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb)

  σπ : (γʰ aʰ bʰ dʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → [ dʰ ] ≡ tʰ (▷ (▷ γʰ aʰ) bʰ)
    → π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ≡ π γʰ (σ γʰ aʰ bʰ) dʰ
  σπ γʰ aʰ bʰ dʰ kγ ka kb kc = mk≡↓ pq qq val≡
    module σπ where
    kδ = k▷ γʰ aʰ kγ ka
    kε = k▷ (▷ γʰ aʰ) bʰ kδ kb
    qq : π γʰ (σ γʰ aʰ bʰ) dʰ ↓
    qq = ∧i con↓ γʰ kγ ,
          ∧i ty↓ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          ∧i ty↓ (▷ γʰ (σ γʰ aʰ bʰ)) dʰ
                 (k▷ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb))
                 (substp (λ x → [ dʰ ] ≡ tʰ x) (σ▷ γʰ aʰ bʰ kγ ka kb) kc) ,
          ∧i conKind γʰ kγ ,
          ∧i tyKind γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          ∧i tyKind (▷ γʰ (σ γʰ aʰ bʰ)) dʰ
                    (k▷ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb))
                    (substp (λ x → [ dʰ ] ≡ tʰ x) (σ▷ γʰ aʰ bʰ kγ ka kb) kc) ,
          tt*
    q : π γʰ (σ γʰ aʰ bʰ) dʰ ↓ → π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ↓
    q _ = ∧i con↓ γʰ kγ ,
          ∧i ty↓ γʰ aʰ kγ ka ,
          ∧i ty↓ (▷ γʰ aʰ) (π (▷ γʰ aʰ) bʰ dʰ) kδ (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kc) ,
          ∧i conKind γʰ kγ ,
          ∧i tyKind γʰ aʰ kγ ka ,
          ∧i tyKind (▷ γʰ aʰ) (π (▷ γʰ aʰ) bʰ dʰ) kδ (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kc) ,
          tt*
    pq : π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ↓
    pq = q qq
    val≡ : π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ! pq ≡ π γʰ (σ γʰ aʰ bʰ) dʰ ! qq
    val≡ =
      σπ₀ (γʰ ! (con↓ γʰ kγ))
          (aʰ ! (ty↓ γʰ aʰ kγ ka))
          (bʰ ! (ty▷↓ γʰ aʰ bʰ kγ ka kδ kb))
          (dʰ ! (ty▷↓ (▷ γʰ aʰ) bʰ dʰ kδ kb kε kc))
          (conKind γʰ kγ)
          (tyKind γʰ aʰ kγ ka)
          (getTy▷-kind γʰ aʰ bʰ kγ ka kδ kb)
          (getTy▷-kind (▷ γʰ aʰ) bʰ dʰ kδ kb kε kc)

  [kʰ]≡kʰ : [ kʰ ] ≡ kʰ
  [kʰ]≡kʰ = mk≡↓ (∧i tt* , tt*) tt* refl

  [∙]≡ĉ : [ ∙ ] ≡ cʰ
  [∙]≡ĉ = mk≡↓ (∧i tt* , tt*) tt* refl

  [▷]≡ĉ : ∀ γ a
    → (kγ : [ γ ] ≡ cʰ)
    → (ka : [ a ] ≡ tʰ γ)
    → [ ▷ γ a ] ≡ cʰ
  [▷]≡ĉ γ a kγ ka =
    mk≡↓ (∧i tt*
         , ∧i con↓ γ kγ
         , ∧i (ty↓ γ a kγ ka)
         , ∧i conKind γ kγ
         , ∧i (tyKind γ a kγ ka)
         , tt*) tt* refl

  tʰ-γ↓ : (γ : CT) → γ ↓ → tʰ γ ↓
  tʰ-γ↓ γ γ↓ = ∧i tt* , γ↓

  ▷-γ : (γ a : CT) → [ ▷ γ a ] ≡ cʰ → [ γ ] ≡ cʰ
  ▷-γ γ a k▷ = mk≡↓ ([]↓ γ γ↓) tt* (▷⁻-kγ γ a ▷↓)
    where
    ▷↓ : ▷ γ a ↓
    ▷↓ = con↓ (▷ γ a) k▷
    γ↓ : γ ↓
    γ↓ = ▷⁻-γ γ a ▷↓

  ▷-a : (γ a : CT) → [ ▷ γ a ] ≡ cʰ → [ a ] ≡ tʰ γ
  ▷-a γ a k▷ = mk≡↓ ([]↓ a a↓) (tʰ-γ↓ γ γ↓) (▷⁻-ka γ a ▷↓)
    where
    ▷↓ : ▷ γ a ↓
    ▷↓ = con↓ (▷ γ a) k▷
    γ↓ : γ ↓
    γ↓ = ▷⁻-γ γ a ▷↓
    a↓ : a ↓
    a↓ = ▷⁻-a γ a ▷↓

  u-γ : (γ : CT) → [ u γ ] ≡ tʰ γ → [ γ ] ≡ cʰ
  u-γ γ ku = mk≡↓ ([]↓ γ γ↓) tt* (u⁻-kγ γ u↓)
    where
    mutual
      [uγ]↓ : [ u γ ] ↓
      [uγ]↓ = extractCond ku (tʰ-γ↓ γ γ↓)
      u↓ : u γ ↓
      u↓ = []⁻ (u γ) [uγ]↓
      γ↓ : γ ↓
      γ↓ = u⁻-γ γ u↓

  π-γ : (γ a b : CT) → [ π γ a b ] ≡ tʰ γ → [ γ ] ≡ cʰ
  π-γ γ a b kπ = mk≡↓ ([]↓ γ γ↓) tt* (π⁻-kγ γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = extractCond kπ (tʰ-γ↓ γ γ↓)
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      γ↓ : γ ↓
      γ↓ = π⁻-γ γ a b π↓

  π-a : (γ a b : CT) → [ π γ a b ] ≡ tʰ γ → [ a ] ≡ tʰ γ
  π-a γ a b kπ = mk≡↓ ([]↓ a a↓) (tʰ-γ↓ γ γ↓) (π⁻-ka γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = extractCond kπ (tʰ-γ↓ γ γ↓)
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      γ↓ : γ ↓
      γ↓ = π⁻-γ γ a b π↓
      a↓ : a ↓
      a↓ = π⁻-a γ a b π↓

  π-b : (γ a b : CT) → [ π γ a b ] ≡ tʰ γ → [ b ] ≡ tʰ (▷ γ a)
  π-b γ a b kπ = mk≡↓ ([]↓ b b↓) (tʰ-γ↓ (▷ γ a) δ↓) (π⁻-kb γ a b π↓)
    where
    mutual
      [πγab]↓ : [ π γ a b ] ↓
      [πγab]↓ = extractCond kπ (tʰ-γ↓ γ γ↓)
      π↓ : π γ a b ↓
      π↓ = []⁻ (π γ a b) [πγab]↓
      γ↓ : γ ↓
      γ↓ = π⁻-γ γ a b π↓
      a↓ : a ↓
      a↓ = π⁻-a γ a b π↓
      b↓ : b ↓
      b↓ = π⁻-b γ a b π↓
      δ↓ : ▷ γ a ↓
      δ↓ = ∧i γ↓ , ∧i a↓ , ∧i π⁻-kγ γ a b π↓ , ∧i π⁻-ka γ a b π↓ , tt*

  σ-γ : (γ a b : CT) → [ σ γ a b ] ≡ tʰ γ → [ γ ] ≡ cʰ
  σ-γ γ a b kσ = mk≡↓ ([]↓ γ γ↓) tt* (σ⁻-kγ γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = extractCond kσ (tʰ-γ↓ γ γ↓)
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      γ↓ : γ ↓
      γ↓ = σ⁻-γ γ a b σ↓

  σ-a : (γ a b : CT) → [ σ γ a b ] ≡ tʰ γ → [ a ] ≡ tʰ γ
  σ-a γ a b kσ = mk≡↓ ([]↓ a a↓) (tʰ-γ↓ γ γ↓) (σ⁻-ka γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = extractCond kσ (tʰ-γ↓ γ γ↓)
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      γ↓ : γ ↓
      γ↓ = σ⁻-γ γ a b σ↓
      a↓ : a ↓
      a↓ = σ⁻-a γ a b σ↓

  σ-b : (γ a b : CT) → [ σ γ a b ] ≡ tʰ γ → [ b ] ≡ tʰ (▷ γ a)
  σ-b γ a b kσ = mk≡↓ ([]↓ b b↓) (tʰ-γ↓ (▷ γ a) δ↓) (σ⁻-kb γ a b σ↓)
    where
    mutual
      [σγab]↓ : [ σ γ a b ] ↓
      [σγab]↓ = extractCond kσ (tʰ-γ↓ γ γ↓)
      σ↓ : σ γ a b ↓
      σ↓ = []⁻ (σ γ a b) [σγab]↓
      γ↓ : γ ↓
      γ↓ = σ⁻-γ γ a b σ↓
      a↓ : a ↓
      a↓ = σ⁻-a γ a b σ↓
      b↓ : b ↓
      b↓ = σ⁻-b γ a b σ↓
      δ↓ : ▷ γ a ↓
      δ↓ = ∧i γ↓ , ∧i a↓ , ∧i σ⁻-kγ γ a b σ↓ , ∧i σ⁻-ka γ a b σ↓ , tt*

  wa : W.Algebra (lsuc ℓA)
  wa = record
    { CT = CT
    ; [_] = [_]
    ; k̂ = kʰ
    ; ĉ = cʰ
    ; t̂ = tʰ
    ; ∙ = ∙
    ; k∙ = k∙
    ; ▷ = ▷
    ; k▷ = k▷
    ; ▷-γ = ▷-γ
    ; ▷-a = ▷-a
    ; u = u
    ; ku = ku
    ; u-γ = u-γ
    ; π = π
    ; kπ = kπ
    ; π-γ = π-γ
    ; π-a = π-a
    ; π-b = π-b
    ; σ = σ
    ; kσ = kσ
    ; σ-γ = σ-γ
    ; σ-a = σ-a
    ; σ-b = σ-b
    ; σ▷ = σ▷
    ; σπ = σπ
    }

G₁ : ∀ {ℓA} {A B : M.Algebra ℓA} → M.Hom A B → W.Hom (G₀ A) (G₀ B)
G₁ {ℓA} {A} {B} f = record
  { θ = θ
  ; [_] = [_]
  ; k̂ = ≡.refl
  ; ĉ = ≡.refl
  ; t̂ = t̂
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
  θ₀ (GA.ty γ a) = GB.ty (f.conᴿ γ) (f.tyᴿ γ a)
  θ₀ (GA.k̂) = GB.k̂
  θ₀ (GA.ĉ) = GB.ĉ
  θ₀ (GA.t̂ γ) = GB.t̂ (θ₀ γ)

  θ : GA.CT → GB.CT
  θ (P ⊢ x) = P ⊢ λ p → θ₀ (x p)

  [_]₀ : ∀ x → θ₀ (GA.[ x ]₀) ≡ GB.[ θ₀ x ]₀
  [ GA.con x ]₀ = ≡.refl
  [ GA.ty γ a ]₀ = ≡.refl
  [ GA.k̂ ]₀ = ≡.refl
  [ GA.ĉ ]₀ = ≡.refl
  [ GA.t̂ γ ]₀ = ≡.refl

  [_] : ∀ (x : GA.CT) → θ (GA.[ x ]) ≡ GB.[ θ x ]
  [ P ⊢ x ] = GB.mkCT≡ (λ p → p) (λ p → p) λ p q → [ x (p .∧e₂) ]₀

  θ-kc : (γ : GA.Atom) → GA.[ γ ]₀ ≡ GA.ĉ → GB.[ θ₀ γ ]₀ ≡ GB.ĉ
  θ-kc γ kγ = ≡.trans (≡.sym [ γ ]₀) (≡.cong θ₀ kγ)

  θ-ka : (γ a : GA.Atom) → GA.[ a ]₀ ≡ GA.t̂ γ → GB.[ θ₀ a ]₀ ≡ GB.t̂ (θ₀ γ)
  θ-ka γ a ka = ≡.trans (≡.sym [ a ]₀) (≡.cong θ₀ ka)

  θ-▷₀ : (γ a : GA.Atom) (kγ : GA.[ γ ]₀ ≡ GA.ĉ) (ka : GA.[ a ]₀ ≡ GA.t̂ γ)
    → θ₀ (GA.▷₀ γ a kγ ka) ≡ GB.▷₀ (θ₀ γ) (θ₀ a) (θ-kc γ kγ) (θ-ka γ a ka)
  θ-▷₀ (GA.con γ) (GA.ty .γ a) ≡.refl ≡.refl = ≡.cong GB.con (f.▷ᴿ γ a)

  θ-kb : (γ a b : GA.Atom) (kγ : GA.[ γ ]₀ ≡ GA.ĉ) (ka : GA.[ a ]₀ ≡ GA.t̂ γ)
    → GA.[ b ]₀ ≡ GA.t̂ (GA.▷₀ γ a kγ ka)
    → GB.[ θ₀ b ]₀ ≡ GB.t̂ (GB.▷₀ (θ₀ γ) (θ₀ a) (θ-kc γ kγ) (θ-ka γ a ka))
  θ-kb γ a b kγ ka kb =
    ≡.trans (≡.sym [ b ]₀) (≡.trans (≡.cong θ₀ kb) (≡.cong GB.t̂ (θ-▷₀ γ a kγ ka)))

  θ-u₀ : (γ : GA.Atom) (kγ : GA.[ γ ]₀ ≡ GA.ĉ)
    → θ₀ (GA.u₀ γ kγ) ≡ GB.u₀ (θ₀ γ) (θ-kc γ kγ)
  θ-u₀ (GA.con γ) ≡.refl = ≡.cong (GB.ty (f.conᴿ γ)) (f.uᴿ γ)

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
