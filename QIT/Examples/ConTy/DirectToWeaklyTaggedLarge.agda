open import QIT.Prelude

module QIT.Examples.ConTy.DirectToWeaklyTaggedLarge
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

open PropExt propExt*
open FunExt funExt*

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

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

G₀ : D.Algebra ℓA → W.Algebra (lsuc ℓA)
G₀ {ℓA} da = wa
  module G₀ where
  open ≡
  open ≡.≡-Reasoning
  module DA = D.Algebra da
  data Atom : Set ℓA where
    con : DA.Con → Atom
    ty : (γ : DA.Con) → DA.Ty γ → Atom
    k̂ : Atom
    ĉ : Atom
    t̂ : Atom → Atom

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
  tʰ : CT → CT
  tʰ = map t̂

  module EncodeAtom where
    Code : Atom → Atom → Prop ℓA
    Code (con γ) (con δ) = γ ≡ δ
    Code (ty γ a) (ty δ b) = γ ≡ δ ∧ᵖ λ p → ≡.subst DA.Ty p a ≡ b
    Code k̂ k̂ = ⊤*
    Code ĉ ĉ = ⊤*
    Code (t̂ x) (t̂ y) = Code x y
    {-# CATCHALL #-}
    Code _ _ = ⊥*

    reflCode : (x : Atom) → Code x x
    reflCode (con γ) = ≡.refl
    reflCode (ty γ a) = ∧i ≡.refl , ≡.refl
    reflCode k̂ = tt*
    reflCode ĉ = tt*
    reflCode (t̂ x) = reflCode x

    encode : ∀ {x y} → x ≡ y → Code x y
    encode {x} refl = reflCode x

    decode : ∀ {x y} → Code x y → x ≡ y
    decode {con γ} {con δ} p = ≡.cong con p
    decode {ty γ a} {ty δ b} (∧i p , q) = dcong₂ ty p q
    decode {k̂} {k̂} p = refl
    decode {ĉ} {ĉ} p = refl
    decode {t̂ x} {t̂ y} p = ≡.cong t̂ (decode p)

    k̂≢ĉ : k̂ ≢ ĉ
    k̂≢ĉ p = ⊥e* (encode p)

    k̂≢t̂ : ∀ {x} → k̂ ≢ t̂ x
    k̂≢t̂ p = ⊥e* (encode p)

    ĉ≢t̂ : ∀ {x} → ĉ ≢ t̂ x
    ĉ≢t̂ p = ⊥e* (encode p)

  open EncodeAtom public

  kʰ≢cʰ : kʰ ≢ cʰ
  kʰ≢cʰ p = k̂≢ĉ (return-inj p)

  kʰ≢tʰ : ∀ {x} → kʰ ≢ tʰ x
  kʰ≢tʰ {x*} =
    ≢sym (map≢return t̂ x* k̂ λ x → ≢sym k̂≢t̂)
    
  cʰ≢tʰ : ∀ {x} → cʰ ≢ tʰ x
  cʰ≢tʰ {x*} =
    ≢sym (map≢return t̂ x* ĉ λ x → ≢sym ĉ≢t̂)

  [_]₀ : Atom → Atom
  [ con γ ]₀ = ĉ
  [ ty γ a ]₀ = t̂ (con γ)
  [ k̂ ]₀ = k̂
  [ ĉ ]₀ = k̂
  [ t̂ γ ]₀ = k̂

  [[x]]₀≡k̂ : ∀ x → [ [ x ]₀ ]₀ ≡ k̂
  [[x]]₀≡k̂ (con γ) = refl
  [[x]]₀≡k̂ (ty γ a) = refl
  [[x]]₀≡k̂ k̂ = refl
  [[x]]₀≡k̂ ĉ = refl
  [[x]]₀≡k̂ (t̂ x) = refl

  [k̂]₀≡k̂ : [ k̂ ]₀ ≡ k̂
  [k̂]₀≡k̂ = refl

  [_] : CT → CT
  [_] = map [_]₀

  con-inj : ∀ {γ δ} → con γ ≡ con δ → γ ≡ δ
  con-inj refl = refl

  ty-inj₁ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ} → ty γ a ≡ ty δ b → γ ≡ δ
  ty-inj₁ refl = refl

  ty-inj₂ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ}
    → (p : ty γ a ≡ ty δ b) → subst DA.Ty (ty-inj₁ p) a ≡ b
  ty-inj₂ refl = refl

  t̂-inj : ∀ {γ δ} → t̂ γ ≡ t̂ δ → γ ≡ δ
  t̂-inj refl = refl

  []₀≡ĉ→con : ∀ {x} → [ x ]₀ ≡ ĉ
    → ΣP DA.Con λ γ
    → x ≡ con γ
  []₀≡ĉ→con {con γ} p = γ , refl

  []₀≡t̂→ty : ∀ {x y} → [ x ]₀ ≡ t̂ y
    → Σ DA.Con λ γ
    → ΣP (DA.Ty γ) λ a
    → x ≡ ty γ a
    ∧ y ≡ con γ
  []₀≡t̂→ty {ty γ a} p = γ , a , ∧i refl , sym (t̂-inj p)

  ConΣ = ΣP Atom λ γ → [ γ ]₀ ≡ ĉ
  ConΣ→Con : ConΣ → DA.Con
  ConΣ→Con (con γ , kγ) = γ
  Con→ConΣ : DA.Con → ConΣ
  Con→ConΣ γ = (con γ , refl)
  TyΣ : (γ : ConΣ) → Set ℓA
  TyΣ γ = ΣP Atom λ a → [ a ]₀ ≡ t̂ (γ .fst)
  TyΣ→Ty : {γ : ConΣ} → TyΣ γ → (DA.Ty (ConΣ→Con γ))
  TyΣ→Ty {con γ , kγ} (ty γ' a , ka) =
    ≡.subst DA.Ty (con-inj (t̂-inj ka)) a
  Ty→TyΣ : {γ : DA.Con} → (a : DA.Ty γ) → TyΣ (Con→ConΣ γ)
  Ty→TyΣ {γ} a = ty γ a , refl

  ConΣ≅Con : ConΣ ≅ˢ DA.Con
  ConΣ≅Con = record
    { to = ConΣ→Con
    ; from = Con→ConΣ
    ; rinv = λ {(con γ , refl) → refl}
    ; linv = λ γ → refl }

  []≡cʰ→return : ∀ {x*} → [ x* ] ≡ cʰ → ΣP DA.Con λ γ → x* ≡ return (con γ)
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
    γ : DA.Con
    γ = []₀≡ĉ→con kx .fst
    x≡conγ : x ≡ con γ
    x≡conγ = []₀≡ĉ→con kx .snd
    x*≡returnγ : x* ≡ return (con γ)
    x*≡returnγ = mk≡↓ x↓ tt* x≡conγ

  []≡tʰ→return
    : ∀ {x* y*}
    → [ x* ] ≡ tʰ y*
    → x* ↓
    → Σ DA.Con λ γ
    → ΣP (DA.Ty γ) λ a
    → x* ≡ return (ty γ a)
    ∧ y* ≡ return (con γ)
  []≡tʰ→return {x*} {y*} p x↓ =
    γ , a , ∧i x*≡return , y*≡return
    where
    p≈ : [ x* ] ≈ tʰ y*
    p≈ = ≡→≈ p
    y↓ : y* ↓
    y↓ =
      (p≈ .∧e₁ .∧e₁ (∧i tt* , x↓)) .∧e₂
    x : Atom
    x = x* ! x↓
    y : Atom
    y = y* ! y↓
    kxy : [ x ]₀ ≡ t̂ y
    kxy =
      p≈ .∧e₂
        (∧i tt* , x↓)
        (∧i tt* , y↓)
    q : Σ DA.Con λ γ
      → ΣP (DA.Ty γ) λ a
      → x ≡ ty γ a ∧ y ≡ con γ
    q = []₀≡t̂→ty kxy
    γ : DA.Con
    γ = q .proj₁
    a : DA.Ty γ
    a = q .proj₂ .fst
    x≡tyγa : x ≡ ty γ a
    x≡tyγa = q .proj₂ .snd .∧e₁
    y≡conγ : y ≡ con γ
    y≡conγ = q .proj₂ .snd .∧e₂
    x*≡return : x* ≡ return (ty γ a)
    x*≡return = mk≡↓ x↓ tt* x≡tyγa
    y*≡return : y* ≡ return (con γ)
    y*≡return = mk≡↓ y↓ tt* y≡conγ

  [kʰ]≢cʰ : [ kʰ ] ≢ cʰ
  [kʰ]≢cʰ p =
    let x , q = map-return-inj [_]₀ kʰ ĉ p
    in ⊥e* (encode q)

  [kʰ]≢tʰ : ∀ {x*} → [ kʰ ] ≢ tʰ x*
  [kʰ]≢tʰ {x*} p = ⊥e* (encode (u .snd))
    where
    u : ΣP Atom (λ x → t̂ x ≡ [ k̂ ]₀)
    u = map-return-inj t̂ x* [ k̂ ]₀ (sym (≡.trans (sym (map-beta [_]₀ k̂)) p))

  [cʰ]≢cʰ : [ cʰ ] ≢ cʰ
  [cʰ]≢cʰ p =
    let x , q = map-return-inj [_]₀ kʰ ĉ p
    in ⊥e* (encode q)

  [cʰ]≢tʰ : ∀ {x*} → [ cʰ ] ≢ tʰ x*
  [cʰ]≢tʰ {x*} p = ⊥e* (encode (u .snd))
    where
    u : ΣP Atom (λ x → t̂ x ≡ [ ĉ ]₀)
    u = map-return-inj t̂ x* [ ĉ ]₀ (sym (≡.trans (sym (map-beta [_]₀ ĉ)) p))

  [tʰ]≢cʰ : ∀ {x*} → [ tʰ x* ] ≢ cʰ
  [tʰ]≢cʰ {x*} p = q (≡.trans (≡.sym (map-fold [_]₀ t̂ x*)) p)
    where
    q : map ([_]₀ ∘ t̂) x* ≢ return ĉ
    q = map≢return ([_]₀ ∘ t̂) x* ĉ λ x ()

  [tʰ]≢tʰ : ∀ {x* y*} → x* ↓ → [ tʰ x* ] ≢ tʰ y*
  [tʰ]≢tʰ {x*} {y*} x↓ p = map≢map ([_]₀ ∘ t̂) t̂ x* y* x↓ (λ _ _ ()) q
    where
    q : map ([_]₀ ∘ t̂) x* ≡ map t̂ y*
    q = trans (sym (map-fold [_]₀ t̂ x*)) p

  [[x]]≢cʰ : ∀ {x*} → [ [ x* ] ] ≢ cʰ
  [[x]]≢cʰ {x*} p =
    map≢return
      ([_]₀ ∘ [_]₀) x* ĉ
      (λ x q → k̂≢ĉ (trans (sym ([[x]]₀≡k̂ x)) q))
      (trans (sym (map-fold [_]₀ [_]₀ x*)) p)

  [[x]]≢tʰ : ∀ {x* y*} → x* ↓ → [ [ x* ] ] ≢ tʰ y*
  [[x]]≢tʰ {x*} {y*} x↓ p =
    map≢map
      ([_]₀ ∘ [_]₀) t̂ x* y* x↓
      (λ x y q → k̂≢t̂ (trans (sym ([[x]]₀≡k̂ x)) q))
      (trans (sym (map-fold [_]₀ [_]₀ x*)) p)

  [[x]]≡kʰ : ∀ x* → x* ↓ → [ [ x* ] ] ≡ kʰ
  [[x]]≡kʰ x* x↓ =
    mk≡↓ (∧i tt* , ∧i tt* , x↓) tt* ([[x]]₀≡k̂ x)
    where
    x : Atom
    x = x* ! x↓

  Con₀ : (γ : Atom) → [ γ ]₀ ≡ ĉ → DA.Con
  Con₀ γ kγ = ConΣ→Con (γ , kγ)

  con-Con₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → con (Con₀ γ kγ) ≡ γ
  con-Con₀ (con γ) refl = refl

  Ty₀ : (γ a : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → [ a ]₀ ≡ t̂ γ → DA.Ty (Con₀ γ kγ)
  Ty₀ γ a kγ ka = TyΣ→Ty {γ = (γ , kγ)} (a , ka)

  ∙₀ : Atom
  ∙₀ = con DA.∙

  ▷₀ : (γ a : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → [ a ]₀ ≡ t̂ γ → Atom
  ▷₀ γ a kγ ka = con (Con₀ γ kγ DA.▷ Ty₀ γ a kγ ka)

  k▷₀ : (γ a : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → (ka : [ a ]₀ ≡ t̂ γ) → [ ▷₀ γ a kγ ka ]₀ ≡ ĉ
  k▷₀ γ a kγ ka = refl

  ▷Σ : (γ : ConΣ) (a : TyΣ γ) → ConΣ
  ▷Σ (γ , kγ) (a , ka) = ▷₀ γ a kγ ka , k▷₀ γ a kγ ka

  u₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → Atom
  u₀ γ kγ = ty (Con₀ γ kγ) (DA.u (Con₀ γ kγ))

  ku₀ : (γ : Atom) → (kγ : [ γ ]₀ ≡ ĉ) → [ u₀ γ kγ ]₀ ≡ t̂ γ
  ku₀ γ kγ = cong t̂ (con-Con₀ γ kγ)

  π₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka)
    → Atom
  π₀ γ a b kγ ka kb =
    ty (Con₀ γ kγ)
      (DA.π (Con₀ γ kγ)
            (Ty₀ γ a kγ ka)
            (Ty₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb))

  kπ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → (kb : [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka))
    → [ π₀ γ a b kγ ka kb ]₀ ≡ t̂ γ
  kπ₀ γ a b kγ ka kb = cong t̂ (con-Con₀ γ kγ)

  Ty₀-π₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → (kb : [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka))
    → Ty₀ γ (π₀ γ a b kγ ka kb) kγ (kπ₀ γ a b kγ ka kb)
    ≡ DA.π (Con₀ γ kγ) (Ty₀ γ a kγ ka) (Ty₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb)
  Ty₀-π₀ (con γ) (ty .γ a) (ty .(γ DA.▷ a) b) refl refl refl = refl

  σ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka)
    → Atom
  σ₀ γ a b kγ ka kb =
    ty (Con₀ γ kγ)
      (DA.σ (Con₀ γ kγ)
            (Ty₀ γ a kγ ka)
            (Ty₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb))

  kσ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → (kb : [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka))
    → [ σ₀ γ a b kγ ka kb ]₀ ≡ t̂ γ
  kσ₀ γ a b kγ ka kb = cong t̂ (con-Con₀ γ kγ)

  Ty₀-σ₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → (kb : [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka))
    → Ty₀ γ (σ₀ γ a b kγ ka kb) kγ (kσ₀ γ a b kγ ka kb)
    ≡ DA.σ (Con₀ γ kγ) (Ty₀ γ a kγ ka) (Ty₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb)
  Ty₀-σ₀ (con γ) (ty .γ a) (ty .(γ DA.▷ a) b) refl refl refl = refl

  σ▷₀ : (γ a b : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → (kb : [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka))
    → ▷₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb
    ≡ ▷₀ γ (σ₀ γ a b kγ ka kb) kγ (kσ₀ γ a b kγ ka kb)
  σ▷₀ (con γ) (ty .γ a) (ty .(γ DA.▷ a) b) refl refl refl =
    cong con (DA.σ▷ γ a b)

  σπ₀ : (γ a b d : Atom)
    → (kγ : [ γ ]₀ ≡ ĉ)
    → (ka : [ a ]₀ ≡ t̂ γ)
    → (kb : [ b ]₀ ≡ t̂ (▷₀ γ a kγ ka))
    → (kd : [ d ]₀ ≡ t̂ (▷₀ (▷₀ γ a kγ ka) b (k▷₀ γ a kγ ka) kb))
    → π₀ γ a (π₀ (▷₀ γ a kγ ka) b d (k▷₀ γ a kγ ka) kb kd)
         kγ ka (kπ₀ (▷₀ γ a kγ ka) b d (k▷₀ γ a kγ ka) kb kd)
      ≡ π₀ γ (σ₀ γ a b kγ ka kb) d
         kγ (kσ₀ γ a b kγ ka kb)
         (trans kd (cong t̂ (σ▷₀ γ a b kγ ka kb)))
  σπ₀ (con γ) (ty .γ a) (ty .(γ DA.▷ a) b) (ty .((γ DA.▷ a) DA.▷ b) d) refl refl refl refl =
    cong (ty γ) (DA.σπ γ a b d)

  con↓ : (γʰ : CT) → [ γʰ ] ≡ cʰ
    → γʰ ↓
  con↓ γʰ kγ = extractCond kγ tt* .∧e₂

  getConAtom : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ)
    → Atom
  getConAtom γʰ kγ = γʰ ! (con↓ γʰ kγ)

  conKind : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ)
    → [ getConAtom γʰ kγ ]₀ ≡ ĉ
  conKind γʰ kγ = extractVal kγ tt*

  getConΣ : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → ConΣ
  getConΣ γʰ kγ = getConAtom γʰ kγ , conKind γʰ kγ 

  getCon : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ) → DA.Con
  getCon γʰ kγ = ConΣ→Con (getConΣ γʰ kγ)

  ty↓ : (γʰ aʰ : CT) (kγ : [ γʰ ] ≡ cʰ) (ka : [ aʰ ] ≡ tʰ γʰ) → aʰ ↓
  ty↓ γʰ aʰ kγ ka = extractCond ka (∧i tt* , con↓ γʰ kγ) .∧e₂

  getTyAtom : (γʰ aʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → Atom
  getTyAtom γʰ aʰ kγ ka = aʰ ! (ty↓ γʰ aʰ kγ ka)

  tyKind : (γʰ aʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → [ getTyAtom γʰ aʰ kγ ka ]₀ ≡ t̂ (getConAtom γʰ kγ)
  tyKind γʰ aʰ kγ ka = extractVal ka (∧i tt* , con↓ γʰ kγ)

  getTyΣ : (γʰ aʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → TyΣ (getConΣ γʰ kγ)
  getTyΣ γʰ aʰ kγ ka = getTyAtom γʰ aʰ kγ ka , tyKind γʰ aʰ kγ ka

  getTy : (γʰ aʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → DA.Ty (getCon γʰ kγ)
  getTy γʰ aʰ kγ ka = TyΣ→Ty (getTyΣ γʰ aʰ kγ ka)

  ∙ : CT
  ∙ = return ∙₀

  ▷ : CT → CT → CT
  ▷ γʰ aʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂ γ) λ ka →
    return (▷₀ γ a kγ ka)

  ▷⁻-γ : ∀ γʰ aʰ
    → (▷ γʰ aʰ) ↓
    → γʰ ↓
  ▷⁻-γ γʰ aʰ ty▷↓ = ty▷↓ .∧e₁
  ▷⁻-a : ∀ γʰ aʰ
    → (▷ γʰ aʰ) ↓
    → aʰ ↓
  ▷⁻-a γʰ aʰ ty▷↓ = ty▷↓ .∧e₂ .∧e₁
  ▷⁻-kγ : ∀ γʰ aʰ
    → (ty▷↓ : (▷ γʰ aʰ) ↓)
    → [ γʰ ! (▷⁻-γ γʰ aʰ ty▷↓) ]₀ ≡ ĉ
  ▷⁻-kγ γʰ aʰ ty▷↓ = ty▷↓ .∧e₂ .∧e₂ .∧e₁
  ▷⁻-ka : ∀ γʰ aʰ
    → (ty▷↓ : (▷ γʰ aʰ) ↓)
    → [ aʰ ! (▷⁻-a γʰ aʰ ty▷↓) ]₀ ≡ t̂ (γʰ ! (▷⁻-γ γʰ aʰ ty▷↓))
  ▷⁻-ka γʰ aʰ ty▷↓ = ty▷↓ .∧e₂ .∧e₂ .∧e₂ .∧e₁

  u : CT → CT
  u γʰ =
    γʰ >>= λ γ →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    return (ty (Con₀ γ kγ) (DA.u (Con₀ γ kγ)))

  u⁻-γ : ∀ γʰ
    → u γʰ ↓
    → γʰ ↓
  u⁻-γ γʰ u↓ = u↓ .∧e₁
  u⁻-kγ : ∀ γʰ
    → (u↓ : u γʰ ↓)
    → [ γʰ ! (u⁻-γ γʰ u↓) ]₀ ≡ ĉ
  u⁻-kγ γʰ u↓ = u↓ .∧e₂ .∧e₁

  π : CT → CT → CT → CT
  π γʰ aʰ bʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    bʰ >>= λ b →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂ γ) λ ka →
    assume ([ b ]₀ ≡ t̂ (▷₀ γ a kγ ka)) λ kb →
    return (ty (Con₀ γ kγ)
               (DA.π (Con₀ γ kγ)
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

  wa : W.Algebra (lsuc ℓA)
  wa = record
    { CT = CT
    ; [_] = [_]
    ; k̂ = kʰ
    ; kk̂ = kk̂
    ; ĉ = cʰ
    ; kĉ = kĉ
    ; t̂ = tʰ
    ; kt̂ = kt̂
    ; ∙ = ∙
    ; k∙ = k∙
    ; ▷ = ▷
    ; k▷ = k▷
    ; u = u
    ; ku = ku
    ; π = π
    ; kπ = kπ
    ; σ = σ
    ; kσ = kσ
    ; σ▷ = σ▷
    ; σπ = σπ
    }

G₁ : ∀ {ℓA} {A B : D.Algebra ℓA} → D.Hom A B → W.Hom (G₀ A) (G₀ B)
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
  module A = D.Algebra A
  module B = D.Algebra B
  module GA = G₀ A
  module GB = G₀ B
  module f = D.Hom f

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

G : ∀ {ℓA} → Functor (D.Cat ℓA) (W.Cat (lsuc ℓA))
G = record
  { ob = G₀
  ; hom = G₁
  ; id = id
  ; comp = comp
  ; resp = resp
  }
  where
  id-θ₀ : ∀ {ℓA} {A : D.Algebra ℓA} (x : G₀.Atom A) → G₁.θ₀ (D.id {A = A}) x ≡ x
  id-θ₀ (G₀.con _) = ≡.refl
  id-θ₀ (G₀.ty _ _) = ≡.refl
  id-θ₀ G₀.k̂ = ≡.refl
  id-θ₀ G₀.ĉ = ≡.refl
  id-θ₀ (G₀.t̂ x) = ≡.cong G₀.t̂ (id-θ₀ x)

  id : ∀ {ℓA} {A : D.Algebra ℓA} → G₁ (D.id {A = A}) W.≈ W.id {A = G₀ A}
  id {ℓA} {A} = W.mk≈ λ { (P ⊢ x) → G₀.mkCT≡ A (λ p → p) (λ p → p) (λ p q → id-θ₀ (x p)) }

  comp-θ₀ : ∀ {ℓA} {A B C : D.Algebra ℓA} (f : D.Hom A B) (g : D.Hom B C) (x : G₀.Atom A)
    → G₁.θ₀ (g D.∘ f) x ≡ G₁.θ₀ g (G₁.θ₀ f x)
  comp-θ₀ f g (G₀.con _) = ≡.refl
  comp-θ₀ f g (G₀.ty _ _) = ≡.refl
  comp-θ₀ f g G₀.k̂ = ≡.refl
  comp-θ₀ f g G₀.ĉ = ≡.refl
  comp-θ₀ f g (G₀.t̂ x) = ≡.cong G₀.t̂ (comp-θ₀ f g x)

  comp : ∀ {ℓA} {A B C : D.Algebra ℓA} (f : D.Hom A B) (g : D.Hom B C)
    → G₁ (g D.∘ f) W.≈ (G₁ g W.∘ G₁ f)
  comp {ℓA} {A} {B} {C} f g = W.mk≈ λ { (P ⊢ x) → G₀.mkCT≡ C (λ p → p) (λ p → p) λ p q → comp-θ₀ f g (x p) }

  resp-θ₀ : ∀ {ℓA} {A B : D.Algebra ℓA} {f g : D.Hom A B} → f D.≈ g → (x : G₀.Atom A)
    → G₁.θ₀ f x ≡ G₁.θ₀ g x
  resp-θ₀ {f = f} {g} p (G₀.con γ) = ≡.cong G₀.con (p .D.con≡ γ)
  resp-θ₀ {f = f} {g} p (G₀.ty γ a) = ≡.dcong₂ G₀.ty (p .D.con≡ γ) (p .D.ty≡ γ a)
  resp-θ₀ p G₀.k̂ = ≡.refl
  resp-θ₀ p G₀.ĉ = ≡.refl
  resp-θ₀ p (G₀.t̂ x) = ≡.cong G₀.t̂ (resp-θ₀ p x)

  resp : ∀ {ℓA} {A B : D.Algebra ℓA} {f g : D.Hom A B} → f D.≈ g → G₁ f W.≈ G₁ g
  resp {ℓA} {A} {B} {f} {g} p = W.mk≈ λ { (P ⊢ x) → G₀.mkCT≡ B (λ q → q) (λ q → q) (λ q r → resp-θ₀ p (x q)) }
