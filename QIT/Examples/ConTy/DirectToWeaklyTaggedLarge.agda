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

G₀ : D.Algebra ℓA → W.Algebra (lsuc ℓA)
G₀ {ℓA} da = wa
  module G₀ where
  open ≡
  module DA = D.Algebra da
  data Atom : Set ℓA where
    con : DA.Con → Atom
    ty : (γ : DA.Con) → DA.Ty γ → Atom
    k̂ : Atom
    ĉ : Atom
    t̂ : Atom → Atom

  mkCT≈ : {P Q : Prop ℓP} {f : P → Atom} {g : Q → Atom}
      → (p→q : P → Q) (q→p : Q → P) (f≡g : ∀ p q → f p ≡ g q)
      → (P , f) ≈ (Q , g)
  mkCT≈ p→q q→p f≡g = ∧i ∧i p→q , q→p , f≡g

  mkCT≡ : {P Q : Prop ℓP} {f : P → Atom} {g : Q → Atom}
      → (p→q : P → Q) (q→p : Q → P) (f≡g : ∀ p q → f p ≡ g q)
      → (P , f) ≡ (Q , g)
  mkCT≡ p→q q→p f≡g = ≈→≡ (∧i ∧i p→q , q→p , f≡g)

  CT = Lifting ℓA Atom

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
  TyΣ : (γ : ConΣ) → Set ℓA
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

  pull₁ : {X : Set ℓA} → {x y : Lifting ℓP X} → x ≡ y
        → (qy : y .proj₁) → x .proj₁
  pull₁ refl qy = qy

  pull₂ : {X : Set ℓA} → {x y : Lifting ℓP X} → (p : x ≡ y)
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
  θ (P , x) = P , λ p → θ₀ (x p)

  [_]₀ : ∀ x → θ₀ (GA.[ x ]₀) ≡ GB.[ θ₀ x ]₀
  [ GA.con x ]₀ = ≡.refl
  [ GA.ty γ a ]₀ = ≡.refl
  [ GA.k̂ ]₀ = ≡.refl
  [ GA.ĉ ]₀ = ≡.refl
  [ GA.t̂ γ ]₀ = ≡.refl

  [_] : ∀ (x : GA.CT) → θ (GA.[ x ]) ≡ GB.[ θ x ]
  [ P , x ] = GB.mkCT≡ (λ p → p) (λ p → p) λ p q → [ x (p .∧e₂) ]₀

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
  t̂ (P , x) = GB.mkCT≡ (λ p → p) (λ p → p) λ p q → ≡.refl

  ∙ : θ GA.∙ ≡ GB.∙
  ∙ = GB.mkCT≡ (λ _ → liftp tt) (λ _ → liftp tt) λ _ _ → ≡.cong GB.con f.∙ᴿ

  ▷ : ∀ (γ : GA.CT) (a : GA.CT)
    → GA.[ γ ] ≡ GA.cʰ
    → GA.[ a ] ≡ GA.tʰ γ
    → θ (GA.▷ γ a) ≡ GB.▷ (θ γ) (θ a)
  ▷ γʰ aʰ kγ ka = GB.mkCT≡ p q pt
    where
    p : proj₁ (θ (GA.▷ γʰ aʰ)) → proj₁ (GB.▷ (θ γʰ) (θ aʰ))
    p (∧i pγ , (∧i pa , (∧i kγ' , (∧i ka' , liftp tt)))) =
      ∧i pγ , ∧i pa , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , ∧i θ-ka (γʰ .proj₂ pγ) (aʰ .proj₂ pa) ka' , liftp tt
    q : proj₁ (GB.▷ (θ γʰ) (θ aʰ)) → proj₁ (θ (GA.▷ γʰ aʰ))
    q _ = ∧i GA.conData₁ γʰ kγ ,
          ∧i GA.tyData₁ γʰ aʰ kγ ka ,
          ∧i GA.conData₂ γʰ kγ ,
          ∧i GA.tyData₂ γʰ aʰ kγ ka ,
          liftp tt
    pt : ∀ p q → θ (GA.▷ γʰ aʰ) .proj₂ p ≡ GB.▷ (θ γʰ) (θ aʰ) .proj₂ q
    pt _ _ = θ-▷₀ (γʰ .proj₂ (GA.conData₁ γʰ kγ)) (aʰ .proj₂ (GA.tyData₁ γʰ aʰ kγ ka)) (GA.conData₂ γʰ kγ) (GA.tyData₂ γʰ aʰ kγ ka)

  u : ∀ (γ : GA.CT) → GA.[ γ ] ≡ GA.cʰ → θ (GA.u γ) ≡ GB.u (θ γ)
  u γʰ kγ = GB.mkCT≡ p q pt
    where
    p : proj₁ (θ (GA.u γʰ)) → proj₁ (GB.u (θ γʰ))
    p (∧i pγ , (∧i kγ' , liftp tt)) = ∧i pγ , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , liftp tt
    q : proj₁ (GB.u (θ γʰ)) → proj₁ (θ (GA.u γʰ))
    q _ = ∧i GA.conData₁ γʰ kγ , ∧i GA.conData₂ γʰ kγ , liftp tt
    pt : ∀ p q → θ (GA.u γʰ) .proj₂ p ≡ GB.u (θ γʰ) .proj₂ q
    pt _ _ = θ-u₀ (γʰ .proj₂ (GA.conData₁ γʰ kγ)) (GA.conData₂ γʰ kγ)

  π : ∀ (γ : GA.CT) (a : GA.CT) (b : GA.CT)
    → GA.[ γ ] ≡ GA.cʰ
    → GA.[ a ] ≡ GA.tʰ γ
    → GA.[ b ] ≡ GA.tʰ (GA.▷ γ a)
    → θ (GA.π γ a b) ≡ GB.π (θ γ) (θ a) (θ b)
  π γʰ aʰ bʰ kγ ka kb = GB.mkCT≡ p q pt
    where
    kδ = GA.k▷ γʰ aʰ kγ ka
    p : proj₁ (θ (GA.π γʰ aʰ bʰ)) → proj₁ (GB.π (θ γʰ) (θ aʰ) (θ bʰ))
    p (∧i pγ , (∧i pa , (∧i pb , (∧i kγ' , (∧i ka' , (∧i kb' , liftp tt)))))) =
      ∧i pγ , ∧i pa , ∧i pb , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , ∧i θ-ka (γʰ .proj₂ pγ) (aʰ .proj₂ pa) ka' , ∧i θ-kb (γʰ .proj₂ pγ) (aʰ .proj₂ pa) (bʰ .proj₂ pb) kγ' ka' kb' , liftp tt
    q : proj₁ (GB.π (θ γʰ) (θ aʰ) (θ bʰ)) → proj₁ (θ (GA.π γʰ aʰ bʰ))
    q _ = ∧i GA.conData₁ γʰ kγ ,
          ∧i GA.tyData₁ γʰ aʰ kγ ka ,
          ∧i GA.extData₁ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i GA.conData₂ γʰ kγ ,
          ∧i GA.tyData₂ γʰ aʰ kγ ka ,
          ∧i GA.extData₂ γʰ aʰ bʰ kγ ka kδ kb ,
          liftp tt
    pt : ∀ p q → θ (GA.π γʰ aʰ bʰ) .proj₂ p ≡ GB.π (θ γʰ) (θ aʰ) (θ bʰ) .proj₂ q
    pt _ _ = θ-π₀ (γʰ .proj₂ (GA.conData₁ γʰ kγ)) (aʰ .proj₂ (GA.tyData₁ γʰ aʰ kγ ka)) (bʰ .proj₂ (GA.extData₁ γʰ aʰ bʰ kγ ka kδ kb)) (GA.conData₂ γʰ kγ) (GA.tyData₂ γʰ aʰ kγ ka) (GA.extData₂ γʰ aʰ bʰ kγ ka kδ kb)

  σ : ∀ (γ : GA.CT) (a : GA.CT) (b : GA.CT)
    → GA.[ γ ] ≡ GA.cʰ
    → GA.[ a ] ≡ GA.tʰ γ
    → GA.[ b ] ≡ GA.tʰ (GA.▷ γ a)
    → θ (GA.σ γ a b) ≡ GB.σ (θ γ) (θ a) (θ b)
  σ γʰ aʰ bʰ kγ ka kb = GB.mkCT≡ p q pt
    where
    kδ = GA.k▷ γʰ aʰ kγ ka
    p : proj₁ (θ (GA.σ γʰ aʰ bʰ)) → proj₁ (GB.σ (θ γʰ) (θ aʰ) (θ bʰ))
    p (∧i pγ , (∧i pa , (∧i pb , (∧i kγ' , (∧i ka' , (∧i kb' , liftp tt)))))) =
      ∧i pγ , ∧i pa , ∧i pb , ∧i θ-kc (γʰ .proj₂ pγ) kγ' , ∧i θ-ka (γʰ .proj₂ pγ) (aʰ .proj₂ pa) ka' , ∧i θ-kb (γʰ .proj₂ pγ) (aʰ .proj₂ pa) (bʰ .proj₂ pb) kγ' ka' kb' , liftp tt
    q : proj₁ (GB.σ (θ γʰ) (θ aʰ) (θ bʰ)) → proj₁ (θ (GA.σ γʰ aʰ bʰ))
    q _ = ∧i GA.conData₁ γʰ kγ ,
          ∧i GA.tyData₁ γʰ aʰ kγ ka ,
          ∧i GA.extData₁ γʰ aʰ bʰ kγ ka kδ kb ,
          ∧i GA.conData₂ γʰ kγ ,
          ∧i GA.tyData₂ γʰ aʰ kγ ka ,
          ∧i GA.extData₂ γʰ aʰ bʰ kγ ka kδ kb ,
          liftp tt
    pt : ∀ p q → θ (GA.σ γʰ aʰ bʰ) .proj₂ p ≡ GB.σ (θ γʰ) (θ aʰ) (θ bʰ) .proj₂ q
    pt _ _ = θ-σ₀ (γʰ .proj₂ (GA.conData₁ γʰ kγ)) (aʰ .proj₂ (GA.tyData₁ γʰ aʰ kγ ka)) (bʰ .proj₂ (GA.extData₁ γʰ aʰ bʰ kγ ka kδ kb)) (GA.conData₂ γʰ kγ) (GA.tyData₂ γʰ aʰ kγ ka) (GA.extData₂ γʰ aʰ bʰ kγ ka kδ kb)

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
  id {ℓA} {A} = W.mk≈ λ { (P , x) → G₀.mkCT≡ A (λ p → p) (λ p → p) (λ p q → id-θ₀ (x p)) }

  comp-θ₀ : ∀ {ℓA} {A B C : D.Algebra ℓA} (f : D.Hom A B) (g : D.Hom B C) (x : G₀.Atom A)
    → G₁.θ₀ (g D.∘ f) x ≡ G₁.θ₀ g (G₁.θ₀ f x)
  comp-θ₀ f g (G₀.con _) = ≡.refl
  comp-θ₀ f g (G₀.ty _ _) = ≡.refl
  comp-θ₀ f g G₀.k̂ = ≡.refl
  comp-θ₀ f g G₀.ĉ = ≡.refl
  comp-θ₀ f g (G₀.t̂ x) = ≡.cong G₀.t̂ (comp-θ₀ f g x)

  comp : ∀ {ℓA} {A B C : D.Algebra ℓA} (f : D.Hom A B) (g : D.Hom B C)
    → G₁ (g D.∘ f) W.≈ (G₁ g W.∘ G₁ f)
  comp {ℓA} {A} {B} {C} f g = W.mk≈ λ { (P , x) → G₀.mkCT≡ C (λ p → p) (λ p → p) λ p q → comp-θ₀ f g (x p) }

  resp-θ₀ : ∀ {ℓA} {A B : D.Algebra ℓA} {f g : D.Hom A B} → f D.≈ g → (x : G₀.Atom A)
    → G₁.θ₀ f x ≡ G₁.θ₀ g x
  resp-θ₀ {f = f} {g} p (G₀.con γ) = ≡.cong G₀.con (p .D.con≡ γ)
  resp-θ₀ {f = f} {g} p (G₀.ty γ a) = ≡.dcong₂ G₀.ty (p .D.con≡ γ) (p .D.ty≡ γ a)
  resp-θ₀ p G₀.k̂ = ≡.refl
  resp-θ₀ p G₀.ĉ = ≡.refl
  resp-θ₀ p (G₀.t̂ x) = ≡.cong G₀.t̂ (resp-θ₀ p x)

  resp : ∀ {ℓA} {A B : D.Algebra ℓA} {f g : D.Hom A B} → f D.≈ g → G₁ f W.≈ G₁ g
  resp {ℓA} {A} {B} {f} {g} p = W.mk≈ λ { (P , x) → G₀.mkCT≡ B (λ q → q) (λ q → q) (λ q r → resp-θ₀ p (x q)) }
