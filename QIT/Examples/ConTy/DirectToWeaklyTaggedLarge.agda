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
open import QIT.LiftingMonad

G₀ : D.Algebra ℓ0 → W.Algebra ℓ1
G₀ da = wa
  module G₀ where
  open ≡
  module DA = D.Algebra da
  data Atom : Set where
    con : DA.Con → Atom
    ty : (γ : DA.Con) → DA.Ty γ → Atom
    k̂ : Atom
    ĉ : Atom
    t̂ : Atom → Atom

  mkCT≈ : {X : Set ℓX} {P Q : Prop ℓP} {f : P → X} {g : Q → X}
      → (p→q : P → Q) (q→p : Q → P) (f≡g : ∀ p q → f p ≡ g q)
      → (P , f) ≈ (Q , g)
  mkCT≈ p→q q→p f≡g = ∧i ∧i p→q , q→p , f≡g

  mkCT≡ : {X : Set ℓX} {P Q : Prop ℓP} {f : P → X} {g : Q → X}
      → (p→q : P → Q) (q→p : Q → P) (f≡g : ∀ p q → f p ≡ g q)
      → (P , f) ≡ (Q , g)
  mkCT≡ p→q q→p f≡g = ≈→≡ (∧i ∧i p→q , q→p , f≡g)

  CT = Lifting ℓ0 Atom

  cʰ : CT
  cʰ = return ĉ
  kʰ : CT
  kʰ = return k̂
  tʰ : CT → CT
  tʰ = map t̂

  [_]₀ : Atom → Atom
  [ con a ]₀ = ĉ
  [ ty γ a ]₀ = t̂ (con γ)
  [ k̂ ]₀ = k̂
  [ ĉ ]₀ = k̂
  [ t̂ γ ]₀ = k̂

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

  ConΣ = ΣP Atom λ γ → [ γ ]₀ ≡ ĉ
  ConΣ→Con : ConΣ → DA.Con
  ConΣ→Con (con γ , kγ) = γ
  TyΣ : (γ : ConΣ) → Set
  TyΣ γ = ΣP Atom λ a → [ a ]₀ ≡ t̂ (γ .fst)
  TyΣ→Ty : {γ : ConΣ} → TyΣ γ → (DA.Ty (ConΣ→Con γ))
  TyΣ→Ty {con γ , kγ} (ty γ' a , ka) =
    ≡.subst DA.Ty (con-inj (t̂-inj ka)) a

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

  pull₁ : {X : Set ℓX} → {x y : Lifting ℓP X} → x ≡ y
        → (qy : y .proj₁) → x .proj₁
  pull₁ refl qy = qy

  pull₂ : {X : Set ℓX} → {x y : Lifting ℓP X} → (p : x ≡ y)
    → (qy : y .proj₁)
    → x .proj₂ (pull₁ p qy) ≡ y .proj₂ qy
  pull₂ refl qy = refl

  conData₁ : (γʰ : CT) → [ γʰ ] ≡ cʰ
    → γʰ .proj₁
  conData₁ γʰ kγ = pull₁ kγ tt* .∧e₂

  conData₂ : (γʰ : CT) → (kγ : [ γʰ ] ≡ cʰ)
    → [ γʰ .proj₂ (conData₁ γʰ kγ) ]₀ ≡ ĉ
  conData₂ γʰ kγ = pull₂ kγ tt*

  tyData₁ : (γʰ aʰ : CT) (kγ : [ γʰ ] ≡ cʰ) (ka : [ aʰ ] ≡ tʰ γʰ)
    → aʰ .proj₁
  tyData₁ γʰ aʰ kγ ka = pull₁ ka (∧i tt* , conData₁ γʰ kγ) .∧e₂

  tyData₂ : (γʰ aʰ : CT) (kγ : [ γʰ ] ≡ cʰ) (ka : [ aʰ ] ≡ tʰ γʰ)
    → [ aʰ .proj₂ (tyData₁ γʰ aʰ kγ ka) ]₀ ≡ t̂ (γʰ .proj₂ (conData₁ γʰ kγ))
  tyData₂ γʰ aʰ kγ ka = pull₂ ka (∧i tt* , conData₁ γʰ kγ)

  ∙ : CT
  ∙ = return ∙₀

  ▷ : CT → CT → CT
  ▷ γʰ aʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂ γ) λ ka →
    return (▷₀ γ a kγ ka)

  u : CT → CT
  u γʰ =
    γʰ >>= λ γ →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    return (ty (Con₀ γ kγ) (DA.u (Con₀ γ kγ)))

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

  σ : CT → CT → CT → CT
  σ γʰ aʰ bʰ =
    γʰ >>= λ γ →
    aʰ >>= λ a →
    bʰ >>= λ b →
    assume ([ γ ]₀ ≡ ĉ) λ kγ →
    assume ([ a ]₀ ≡ t̂ γ) λ ka →
    assume ([ b ]₀ ≡ t̂ (▷₀ γ a kγ ka)) λ kb →
    return (σ₀ γ a b kγ ka kb)

  extData₁ : (γʰ aʰ bʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → (kδ : [ ▷ γʰ aʰ ] ≡ cʰ)
    → (kb : [ bʰ ] ≡ tʰ (▷ γʰ aʰ))
    → bʰ .proj₁
  extData₁ γʰ aʰ bʰ kγ ka kδ kb = pull₁ kb (∧i tt* , conData₁ (▷ γʰ aʰ) kδ) .∧e₂

  extData₂ : (γʰ aʰ bʰ : CT)
    → (kγ : [ γʰ ] ≡ cʰ)
    → (ka : [ aʰ ] ≡ tʰ γʰ)
    → (kδ : [ ▷ γʰ aʰ ] ≡ cʰ)
    → (kb : [ bʰ ] ≡ tʰ (▷ γʰ aʰ))
    → [ bʰ .proj₂ (extData₁ γʰ aʰ bʰ kγ ka kδ kb) ]₀
    ≡ t̂ (▷₀ (γʰ .proj₂ (conData₁ γʰ kγ))
             (aʰ .proj₂ (tyData₁ γʰ aʰ kγ ka))
             (conData₂ γʰ kγ)
             (tyData₂ γʰ aʰ kγ ka))
  extData₂ γʰ aʰ bʰ kγ ka kδ kb = tyData₂ (▷ γʰ aʰ) bʰ kδ kb

  kk̂ : [ kʰ ] ≡ kʰ
  kk̂ = mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , tt*) λ _ _ → refl

  kĉ : [ cʰ ] ≡ kʰ
  kĉ = mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , tt*) λ _ _ → refl

  kt̂ : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ tʰ γʰ ] ≡ kʰ
  kt̂ γʰ kγ = mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , ∧i tt* , conData₁ γʰ kγ) λ _ _ → refl

  k∙ : [ ∙ ] ≡ cʰ
  k∙ = ≈→≡ (∧i (∧i (λ _ → tt*) , (λ _ → ∧i tt* , tt*)) , (λ _ _ → refl))

  k▷ : (γʰ aʰ : CT) → [ γʰ ] ≡ cʰ → [ aʰ ] ≡ tʰ γʰ → [ ▷ γʰ aʰ ] ≡ cʰ
  k▷ γʰ aʰ kγ ka = mkCT≡ p q λ _ _ → refl
    module k▷ where
    p : proj₁ (return [_]₀) ∧ᵖ (λ h* → proj₁ (▷ γʰ aʰ)) → ⊤*
    p _ = tt*
    q : LiftP ℓ0 ⊤ → proj₁ (return [_]₀) ∧ᵖ (λ h* → proj₁ (▷ γʰ aʰ))
    q _ = ∧i tt* ,
          ∧i conData₁ γʰ kγ ,
          ∧i tyData₁ γʰ aʰ kγ ka ,
          ∧i conData₂ γʰ kγ ,
          ∧i tyData₂ γʰ aʰ kγ ka ,
          tt*

  ku : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ u γʰ ] ≡ tʰ γʰ
  ku γʰ kγ = mkCT≡ p q pt
    module ku where
    p : proj₁ [ u γʰ ] → proj₁ (tʰ γʰ)
    p _ = ∧i tt* , conData₁ γʰ kγ
    q : proj₁ (tʰ γʰ) → proj₁ [ u γʰ ]
    q _ = ∧i tt* , ∧i conData₁ γʰ kγ , ∧i conData₂ γʰ kγ , tt*
    pt : ∀ p q → [ u γʰ ] .proj₂ p ≡ tʰ γʰ .proj₂ q
    pt _ _ =
      trans (ku₀ (γʰ .proj₂ (conData₁ γʰ kγ)) (conData₂ γʰ kγ))
            (cong t̂ (congp (γʰ .proj₂)))

  kπ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → [ π γʰ aʰ bʰ ] ≡ tʰ γʰ
  kπ γʰ aʰ bʰ kγ ka kb = mkCT≡ p q pt
    module kπ where
    kδ = k▷ γʰ aʰ kγ ka
    p : proj₁ [ π γʰ aʰ bʰ ] → proj₁ (tʰ γʰ)
    p _ = ∧i tt* , conData₁ γʰ kγ
    q : proj₁ (tʰ γʰ) → proj₁ [ π γʰ aʰ bʰ ]
    q _ = ∧i tt* ,
          ∧i conData₁ γʰ kγ ,
          ∧i tyData₁ γʰ aʰ kγ ka ,
          ∧i extData₁ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i conData₂ γʰ kγ ,
          ∧i tyData₂ γʰ aʰ kγ ka ,
          ∧i extData₂ γʰ aʰ bʰ kγ ka kδ kb ,
          tt*
    pt : ∀ p q → [ π γʰ aʰ bʰ ] .proj₂ p ≡ tʰ γʰ .proj₂ q
    pt _ _ =
      trans (kπ₀ (γʰ .proj₂ (conData₁ γʰ kγ))
                  (aʰ .proj₂ (tyData₁ γʰ aʰ kγ ka))
                  (bʰ .proj₂ (extData₁ γʰ aʰ bʰ kγ ka kδ kb))
                  (conData₂ γʰ kγ)
                  (tyData₂ γʰ aʰ kγ ka)
                  (extData₂ γʰ aʰ bʰ kγ ka kδ kb))
            (cong t̂ (congp (γʰ .proj₂)))

  kσ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → [ σ γʰ aʰ bʰ ] ≡ tʰ γʰ
  kσ γʰ aʰ bʰ kγ ka kb = mkCT≡ p q pt
    module kσ where
    kδ = k▷ γʰ aʰ kγ ka
    p : proj₁ [ σ γʰ aʰ bʰ ] → proj₁ (tʰ γʰ)
    p _ = ∧i tt* , conData₁ γʰ kγ
    q : proj₁ (tʰ γʰ) → proj₁ [ σ γʰ aʰ bʰ ]
    q _ = ∧i tt* ,
          ∧i conData₁ γʰ kγ ,
          ∧i tyData₁ γʰ aʰ kγ ka ,
          ∧i extData₁ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i conData₂ γʰ kγ ,
          ∧i tyData₂ γʰ aʰ kγ ka ,
          ∧i extData₂ γʰ aʰ bʰ kγ ka kδ kb ,
          tt*
    pt : ∀ p q → [ σ γʰ aʰ bʰ ] .proj₂ p ≡ tʰ γʰ .proj₂ q
    pt _ _ =
      trans (kσ₀ (γʰ .proj₂ (conData₁ γʰ kγ))
                  (aʰ .proj₂ (tyData₁ γʰ aʰ kγ ka))
                  (bʰ .proj₂ (extData₁ γʰ aʰ bʰ kγ ka kδ kb))
                  (conData₂ γʰ kγ)
                  (tyData₂ γʰ aʰ kγ ka)
                  (extData₂ γʰ aʰ bʰ kγ ka kδ kb))
            (cong t̂ (congp (γʰ .proj₂)))

  σ▷ : (γʰ aʰ bʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → ▷ (▷ γʰ aʰ) bʰ ≡ ▷ γʰ (σ γʰ aʰ bʰ)
  σ▷ γʰ aʰ bʰ kγ ka kb = mkCT≡ p q pt
    module σ▷ where
    kδ = k▷ γʰ aʰ kγ ka
    p : proj₁ (▷ (▷ γʰ aʰ) bʰ) → proj₁ (▷ γʰ (σ γʰ aʰ bʰ))
    p _ = ∧i conData₁ γʰ kγ ,
          ∧i tyData₁ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          ∧i conData₂ γʰ kγ ,
          ∧i tyData₂ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          tt*
    q : proj₁ (▷ γʰ (σ γʰ aʰ bʰ)) → proj₁ (▷ (▷ γʰ aʰ) bʰ)
    q _ = ∧i conData₁ (▷ γʰ aʰ) kδ ,
          ∧i tyData₁ (▷ γʰ aʰ) bʰ kδ kb ,
          ∧i conData₂ (▷ γʰ aʰ) kδ ,
          ∧i tyData₂ (▷ γʰ aʰ) bʰ kδ kb ,
          tt*
    pt : ∀ p q → ▷ (▷ γʰ aʰ) bʰ .proj₂ p ≡ ▷ γʰ (σ γʰ aʰ bʰ) .proj₂ q
    pt _ _ =
      σ▷₀ (γʰ .proj₂ (conData₁ γʰ kγ))
          (aʰ .proj₂ (tyData₁ γʰ aʰ kγ ka))
          (bʰ .proj₂ (extData₁ γʰ aʰ bʰ kγ ka kδ kb))
          (conData₂ γʰ kγ)
          (tyData₂ γʰ aʰ kγ ka)
          (extData₂ γʰ aʰ bʰ kγ ka kδ kb)

  σπ : (γʰ aʰ bʰ dʰ : CT)
    → [ γʰ ] ≡ cʰ
    → [ aʰ ] ≡ tʰ γʰ
    → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
    → [ dʰ ] ≡ tʰ (▷ (▷ γʰ aʰ) bʰ)
    → π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) ≡ π γʰ (σ γʰ aʰ bʰ) dʰ
  σπ γʰ aʰ bʰ dʰ kγ ka kb kc = mkCT≡ p q pt
    module σπ where
    kδ = k▷ γʰ aʰ kγ ka
    kε = k▷ (▷ γʰ aʰ) bʰ kδ kb
    p : proj₁ (π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ)) → proj₁ (π γʰ (σ γʰ aʰ bʰ) dʰ)
    p _ = ∧i conData₁ γʰ kγ ,
          ∧i tyData₁ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          ∧i tyData₁ (▷ γʰ (σ γʰ aʰ bʰ)) dʰ (k▷ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb)) (substp (λ x → [ dʰ ] ≡ tʰ x) (σ▷ γʰ aʰ bʰ kγ ka kb) kc) ,
          ∧i conData₂ γʰ kγ ,
          ∧i tyData₂ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb) ,
          ∧i tyData₂ (▷ γʰ (σ γʰ aʰ bʰ)) dʰ (k▷ γʰ (σ γʰ aʰ bʰ) kγ (kσ γʰ aʰ bʰ kγ ka kb)) (substp (λ x → [ dʰ ] ≡ tʰ x) (σ▷ γʰ aʰ bʰ kγ ka kb) kc) ,
          tt*
    q : proj₁ (π γʰ (σ γʰ aʰ bʰ) dʰ) → proj₁ (π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ))
    q _ = ∧i conData₁ γʰ kγ ,
          ∧i tyData₁ γʰ aʰ kγ ka ,
          ∧i tyData₁ (▷ γʰ aʰ) (π (▷ γʰ aʰ) bʰ dʰ) kδ (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kc) ,
          ∧i conData₂ γʰ kγ ,
          ∧i tyData₂ γʰ aʰ kγ ka ,
          ∧i tyData₂ (▷ γʰ aʰ) (π (▷ γʰ aʰ) bʰ dʰ) kδ (kπ (▷ γʰ aʰ) bʰ dʰ kδ kb kc) ,
          tt*
    pt : ∀ p q → π γʰ aʰ (π (▷ γʰ aʰ) bʰ dʰ) .proj₂ p ≡ π γʰ (σ γʰ aʰ bʰ) dʰ .proj₂ q
    pt _ _ =
      σπ₀ (γʰ .proj₂ (conData₁ γʰ kγ))
          (aʰ .proj₂ (tyData₁ γʰ aʰ kγ ka))
          (bʰ .proj₂ (extData₁ γʰ aʰ bʰ kγ ka kδ kb))
          (dʰ .proj₂ (extData₁ (▷ γʰ aʰ) bʰ dʰ kδ kb kε kc))
          (conData₂ γʰ kγ)
          (tyData₂ γʰ aʰ kγ ka)
          (extData₂ γʰ aʰ bʰ kγ ka kδ kb)
          (extData₂ (▷ γʰ aʰ) bʰ dʰ kδ kb kε kc)

  wa : W.Algebra ℓ1
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

G₁ : ∀ {α β : D.Algebra ℓ0} → D.Hom α β → W.Hom (G₀ α) (G₀ β)
G₁ {α} {β} f = record
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
  module α = D.Algebra α
  module β = D.Algebra β
  module A = G₀ α
  module B = G₀ β
  module f = D.Hom f

  θ₀ : A.Atom → B.Atom
  θ₀ (A.con γ) = B.con (f.conᴿ γ)
  θ₀ (A.ty γ a) = B.ty (f.conᴿ γ) (f.tyᴿ γ a)
  θ₀ A.k̂ = B.k̂
  θ₀ A.ĉ = B.ĉ
  θ₀ (A.t̂ γ) = B.t̂ (θ₀ γ)

  θ : A.CT → B.CT
  θ (P , x) = P , λ p → θ₀ (x p)

  [_]₀ : ∀ x → θ₀ (A.[ x ]₀) ≡ B.[ θ₀ x ]₀
  [ A.con x ]₀ = ≡.refl
  [ A.ty γ a ]₀ = ≡.refl
  [ A.k̂ ]₀ = ≡.refl
  [ A.ĉ ]₀ = ≡.refl
  [ A.t̂ γ ]₀ = ≡.refl

  [_] : ∀ (x : A.CT) → θ (A.[ x ]) ≡ B.[ θ x ]
  [ P , x ] = B.mkCT≡ (λ p → p) (λ p → p) λ p q → [ x (p .∧e₂) ]₀

  θ-kc : (γ : A.Atom) → A.[ γ ]₀ ≡ A.ĉ → B.[ θ₀ γ ]₀ ≡ B.ĉ
  θ-kc γ kγ = ≡.trans (≡.sym [ γ ]₀) (≡.cong θ₀ kγ)

  θ-ka : (γ a : A.Atom) → A.[ a ]₀ ≡ A.t̂ γ → B.[ θ₀ a ]₀ ≡ B.t̂ (θ₀ γ)
  θ-ka γ a ka = ≡.trans (≡.sym [ a ]₀) (≡.cong θ₀ ka)

  θ-▷₀ : (γ a : A.Atom) (kγ : A.[ γ ]₀ ≡ A.ĉ) (ka : A.[ a ]₀ ≡ A.t̂ γ)
    → θ₀ (A.▷₀ γ a kγ ka) ≡ B.▷₀ (θ₀ γ) (θ₀ a) (θ-kc γ kγ) (θ-ka γ a ka)
  θ-▷₀ (A.con γ) (A.ty .γ a) ≡.refl ≡.refl = ≡.cong B.con (f.▷ᴿ γ a)

  θ-kb : (γ a b : A.Atom) (kγ : A.[ γ ]₀ ≡ A.ĉ) (ka : A.[ a ]₀ ≡ A.t̂ γ)
    → A.[ b ]₀ ≡ A.t̂ (A.▷₀ γ a kγ ka)
    → B.[ θ₀ b ]₀ ≡ B.t̂ (B.▷₀ (θ₀ γ) (θ₀ a) (θ-kc γ kγ) (θ-ka γ a ka))
  θ-kb γ a b kγ ka kb =
    ≡.trans (≡.sym [ b ]₀) (≡.trans (≡.cong θ₀ kb) (≡.cong B.t̂ (θ-▷₀ γ a kγ ka)))

  θ-u₀ : (γ : A.Atom) (kγ : A.[ γ ]₀ ≡ A.ĉ)
    → θ₀ (A.u₀ γ kγ) ≡ B.u₀ (θ₀ γ) (θ-kc γ kγ)
  θ-u₀ (A.con γ) ≡.refl = ≡.cong (B.ty (f.conᴿ γ)) (f.uᴿ γ)

  θ-π₀ : (γ a b : A.Atom) (kγ : A.[ γ ]₀ ≡ A.ĉ) (ka : A.[ a ]₀ ≡ A.t̂ γ)
    (kb : A.[ b ]₀ ≡ A.t̂ (A.▷₀ γ a kγ ka))
    → θ₀ (A.π₀ γ a b kγ ka kb)
    ≡ B.π₀ (θ₀ γ) (θ₀ a) (θ₀ b) (θ-kc γ kγ) (θ-ka γ a ka) (θ-kb γ a b kγ ka kb)
  θ-π₀ (A.con γ) (A.ty .γ a) (A.ty .(γ α.▷ a) b) ≡.refl ≡.refl ≡.refl =
    ≡.cong (B.ty (f.conᴿ γ)) (f.πᴿ γ a b)

  θ-σ₀ : (γ a b : A.Atom) (kγ : A.[ γ ]₀ ≡ A.ĉ) (ka : A.[ a ]₀ ≡ A.t̂ γ)
    (kb : A.[ b ]₀ ≡ A.t̂ (A.▷₀ γ a kγ ka))
    → θ₀ (A.σ₀ γ a b kγ ka kb)
    ≡ B.σ₀ (θ₀ γ) (θ₀ a) (θ₀ b) (θ-kc γ kγ) (θ-ka γ a ka) (θ-kb γ a b kγ ka kb)
  θ-σ₀ (A.con γ) (A.ty .γ a) (A.ty .(γ α.▷ a) b) ≡.refl ≡.refl ≡.refl =
    ≡.cong (B.ty (f.conᴿ γ)) (f.σᴿ γ a b)

  t̂ : ∀ γ → θ (A.tʰ γ) ≡ B.tʰ (θ γ)
  t̂ (P , x) = B.mkCT≡ (λ p → p) (λ p → p) λ p q → ≡.refl

  ∙ : θ A.∙ ≡ B.∙
  ∙ = B.mkCT≡ (λ _ → tt*) (λ _ → tt*) λ _ _ → ≡.cong B.con f.∙ᴿ

  ▷ : ∀ (γ : A.CT) (a : A.CT)
    → A.[ γ ] ≡ A.cʰ
    → A.[ a ] ≡ A.tʰ γ
    → θ (A.▷ γ a) ≡ B.▷ (θ γ) (θ a)
  ▷ γʰ aʰ kγ ka = B.mkCT≡ p q pt
    where
    p : proj₁ (θ (A.▷ γʰ aʰ)) → proj₁ (B.▷ (θ γʰ) (θ aʰ))
    p (∧i pγ , (∧i pa , (∧i kγ' , (∧i ka' , tt*)))) =
      ∧i pγ , ∧i pa , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , ∧i θ-ka (γʰ .proj₂ pγ) (aʰ .proj₂ pa) ka' , tt*
    q : proj₁ (B.▷ (θ γʰ) (θ aʰ)) → proj₁ (θ (A.▷ γʰ aʰ))
    q _ = ∧i A.conData₁ γʰ kγ ,
          ∧i A.tyData₁ γʰ aʰ kγ ka ,
          ∧i A.conData₂ γʰ kγ ,
          ∧i A.tyData₂ γʰ aʰ kγ ka ,
          tt*
    pt : ∀ p q → θ (A.▷ γʰ aʰ) .proj₂ p ≡ B.▷ (θ γʰ) (θ aʰ) .proj₂ q
    pt _ _ = θ-▷₀ (γʰ .proj₂ (A.conData₁ γʰ kγ)) (aʰ .proj₂ (A.tyData₁ γʰ aʰ kγ ka)) (A.conData₂ γʰ kγ) (A.tyData₂ γʰ aʰ kγ ka)

  u : ∀ (γ : A.CT) → A.[ γ ] ≡ A.cʰ → θ (A.u γ) ≡ B.u (θ γ)
  u γʰ kγ = B.mkCT≡ p q pt
    where
    p : proj₁ (θ (A.u γʰ)) → proj₁ (B.u (θ γʰ))
    p (∧i pγ , (∧i kγ' , tt*)) = ∧i pγ , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , tt*
    q : proj₁ (B.u (θ γʰ)) → proj₁ (θ (A.u γʰ))
    q _ = ∧i A.conData₁ γʰ kγ , ∧i A.conData₂ γʰ kγ , tt*
    pt : ∀ p q → θ (A.u γʰ) .proj₂ p ≡ B.u (θ γʰ) .proj₂ q
    pt _ _ = θ-u₀ (γʰ .proj₂ (A.conData₁ γʰ kγ)) (A.conData₂ γʰ kγ)

  π : ∀ (γ : A.CT) (a : A.CT) (b : A.CT)
    → A.[ γ ] ≡ A.cʰ
    → A.[ a ] ≡ A.tʰ γ
    → A.[ b ] ≡ A.tʰ (A.▷ γ a)
    → θ (A.π γ a b) ≡ B.π (θ γ) (θ a) (θ b)
  π γʰ aʰ bʰ kγ ka kb = B.mkCT≡ p q pt
    where
    kδ = A.k▷ γʰ aʰ kγ ka
    p : proj₁ (θ (A.π γʰ aʰ bʰ)) → proj₁ (B.π (θ γʰ) (θ aʰ) (θ bʰ))
    p (∧i pγ , (∧i pa , (∧i pb , (∧i kγ' , (∧i ka' , (∧i kb' , tt*)))))) =
      ∧i pγ , ∧i pa , ∧i pb , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , ∧i θ-ka (γʰ .proj₂ pγ) (aʰ .proj₂ pa) ka' , ∧i θ-kb (γʰ .proj₂ pγ) (aʰ .proj₂ pa) (bʰ .proj₂ pb) kγ' ka' kb' , tt*
    q : proj₁ (B.π (θ γʰ) (θ aʰ) (θ bʰ)) → proj₁ (θ (A.π γʰ aʰ bʰ))
    q _ = ∧i A.conData₁ γʰ kγ ,
          ∧i A.tyData₁ γʰ aʰ kγ ka ,
          ∧i A.extData₁ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i A.conData₂ γʰ kγ ,
          ∧i A.tyData₂ γʰ aʰ kγ ka ,
          ∧i A.extData₂ γʰ aʰ bʰ kγ ka kδ kb ,
          tt*
    pt : ∀ p q → θ (A.π γʰ aʰ bʰ) .proj₂ p ≡ B.π (θ γʰ) (θ aʰ) (θ bʰ) .proj₂ q
    pt _ _ = θ-π₀ (γʰ .proj₂ (A.conData₁ γʰ kγ)) (aʰ .proj₂ (A.tyData₁ γʰ aʰ kγ ka)) (bʰ .proj₂ (A.extData₁ γʰ aʰ bʰ kγ ka kδ kb)) (A.conData₂ γʰ kγ) (A.tyData₂ γʰ aʰ kγ ka) (A.extData₂ γʰ aʰ bʰ kγ ka kδ kb)

  σ : ∀ (γ : A.CT) (a : A.CT) (b : A.CT)
    → A.[ γ ] ≡ A.cʰ
    → A.[ a ] ≡ A.tʰ γ
    → A.[ b ] ≡ A.tʰ (A.▷ γ a)
    → θ (A.σ γ a b) ≡ B.σ (θ γ) (θ a) (θ b)
  σ γʰ aʰ bʰ kγ ka kb = B.mkCT≡ p q pt
    where
    kδ = A.k▷ γʰ aʰ kγ ka
    p : proj₁ (θ (A.σ γʰ aʰ bʰ)) → proj₁ (B.σ (θ γʰ) (θ aʰ) (θ bʰ))
    p (∧i pγ , (∧i pa , (∧i pb , (∧i kγ' , (∧i ka' , (∧i kb' , tt*)))))) =
      ∧i pγ , ∧i pa , ∧i pb , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , ∧i θ-ka (γʰ .proj₂ pγ) (aʰ .proj₂ pa) ka' , ∧i θ-kb (γʰ .proj₂ pγ) (aʰ .proj₂ pa) (bʰ .proj₂ pb) kγ' ka' kb' , tt*
    q : proj₁ (B.σ (θ γʰ) (θ aʰ) (θ bʰ)) → proj₁ (θ (A.σ γʰ aʰ bʰ))
    q _ = ∧i A.conData₁ γʰ kγ ,
          ∧i A.tyData₁ γʰ aʰ kγ ka ,
          ∧i A.extData₁ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i A.conData₂ γʰ kγ ,
          ∧i A.tyData₂ γʰ aʰ kγ ka ,
          ∧i A.extData₂ γʰ aʰ bʰ kγ ka kδ kb ,
          tt*
    pt : ∀ p q → θ (A.σ γʰ aʰ bʰ) .proj₂ p ≡ B.σ (θ γʰ) (θ aʰ) (θ bʰ) .proj₂ q
    pt _ _ = θ-σ₀ (γʰ .proj₂ (A.conData₁ γʰ kγ)) (aʰ .proj₂ (A.tyData₁ γʰ aʰ kγ ka)) (bʰ .proj₂ (A.extData₁ γʰ aʰ bʰ kγ ka kδ kb)) (A.conData₂ γʰ kγ) (A.tyData₂ γʰ aʰ kγ ka) (A.extData₂ γʰ aʰ bʰ kγ ka kδ kb)

G : Functor (D.Cat ℓ0) (W.Cat ℓ1)
G = record
  { ob = G₀
  ; hom = G₁
  ; id = id
  ; comp = comp
  ; resp = resp
  }
  where
  id-θ₀ : ∀ {α : D.Algebra ℓ0} (x : G₀.Atom α) → G₁.θ₀ (D.id {A = α}) x ≡ x
  id-θ₀ (G₀.con _) = ≡.refl
  id-θ₀ (G₀.ty _ _) = ≡.refl
  id-θ₀ G₀.k̂ = ≡.refl
  id-θ₀ G₀.ĉ = ≡.refl
  id-θ₀ (G₀.t̂ x) = ≡.cong G₀.t̂ (id-θ₀ x)

  id : ∀ {α : D.Algebra ℓ0} → G₁ (D.id {A = α}) W.≈ W.id {α = G₀ α}
  id {α} = W.mk≈ λ { (P , x) → A.mkCT≡ (λ p → p) (λ p → p) (λ p q → id-θ₀ (x p)) }
    where module A = G₀ α

  comp-θ₀ : ∀ {α β γ : D.Algebra ℓ0} (f : D.Hom α β) (g : D.Hom β γ) (x : G₀.Atom α)
    → G₁.θ₀ (g D.∘ f) x ≡ G₁.θ₀ g (G₁.θ₀ f x)
  comp-θ₀ f g (G₀.con _) = ≡.refl
  comp-θ₀ f g (G₀.ty _ _) = ≡.refl
  comp-θ₀ f g G₀.k̂ = ≡.refl
  comp-θ₀ f g G₀.ĉ = ≡.refl
  comp-θ₀ f g (G₀.t̂ x) = ≡.cong G₀.t̂ (comp-θ₀ f g x)

  comp : ∀ {α β γ : D.Algebra ℓ0} (f : D.Hom α β) (g : D.Hom β γ)
    → G₁ (g D.∘ f) W.≈ (G₁ g W.∘ G₁ f)
  comp {α} f g = W.mk≈ λ { (P , x) → A.mkCT≡ (λ p → p) (λ p → p) (λ p q → comp-θ₀ f g (x p)) }
    where module A = G₀ α

  resp-θ₀ : ∀ {α β : D.Algebra ℓ0} {f g : D.Hom α β} → f D.≈ g → (x : G₀.Atom α)
    → G₁.θ₀ f x ≡ G₁.θ₀ g x
  resp-θ₀ {f = f} {g} p (G₀.con γ) = ≡.cong G₀.con (p .D.con≡ γ)
  resp-θ₀ {f = f} {g} p (G₀.ty γ a) = ≡.dcong₂ G₀.ty (p .D.con≡ γ) (p .D.ty≡ γ a)
  resp-θ₀ p G₀.k̂ = ≡.refl
  resp-θ₀ p G₀.ĉ = ≡.refl
  resp-θ₀ p (G₀.t̂ x) = ≡.cong G₀.t̂ (resp-θ₀ p x)

  resp : ∀ {α β : D.Algebra ℓ0} {f g : D.Hom α β} → f D.≈ g → G₁ f W.≈ G₁ g
  resp {α} {β} {f} {g} p = W.mk≈ λ { (P , x) → A.mkCT≡ (λ q → q) (λ q → q) (λ q r → resp-θ₀ p (x q)) }
    where module A = G₀ α
