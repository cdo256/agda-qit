open import QIT.Prelude

module QIT.Examples.ConTy.DirectToWeaklyTagged2
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

D→W : D.Algebra → W.Algebra
D→W da = {!wa!}
  where
  open ≡
  module DA = D.Algebra da
  data Atom : Set where
    con : DA.Con → Atom
    ty : (γ : DA.Con) → DA.Ty γ → Atom
    k̂ : Atom
    ĉ : Atom
    t̂ : Atom → Atom

  Lifting : ∀ ℓP (X : Set ℓX) → Set (lsuc ℓP ⊔ ℓX)
  Lifting ℓP X = Σ (Prop ℓP) (λ P → P → X)

  return : {X : Set ℓX} → X → Lifting ℓP X
  return x = ⊤* , λ _ → x
  fail : {X : Set ℓX} → Lifting ℓP X
  fail = ⊥* , λ ()
  assume : {X : Set ℓX} → (P : Prop ℓP) → (P → Lifting ℓP X) → Lifting ℓP X
  assume P x = (P ∧ᵖ (λ p → x p .proj₁)) , λ (∧i p , hx) → x p .proj₂  hx
  _>>=_ : {X : Set ℓX} {Y : Set ℓY} → Lifting ℓP X → (X → Lifting ℓP Y) → Lifting ℓP Y
  (hs , x) >>= f = (hs ∧ᵖ λ h* → f (x h*) .proj₁) , λ h* → f (x (h* .∧e₁)) .proj₂ (h* .∧e₂)
  _>>_ : {X : Set ℓX} {Y : Set ℓY} → Lifting ℓP X → Lifting ℓP Y → Lifting ℓP Y
  x >> y = x >>= λ _ → y
  _<*>_ : {X : Set ℓX} {Y : Set ℓY} → Lifting ℓP (X → Y) → Lifting ℓP X → Lifting ℓP Y
  _<*>_ (hs , f) (gs , x) = (hs , f) >>= λ f → gs , λ g* → f (x g*)
  map : {X : Set ℓX} {Y : Set ℓY} → (X → Y) → Lifting ℓP X → Lifting ℓP Y
  map f x = return f <*> x

  _≈_ : ∀ {X : Set ℓX} → Lifting ℓP X → Lifting ℓP X → Prop _
  (P , f) ≈ (Q , g) =
    (P ⇔ Q) ∧ ∀ p q → f p ≡ g q

  ≈→≡ : ∀ {X : Set ℓX} → {x y : Lifting ℓP X} → x ≈ y → x ≡ y
  ≈→≡ {X = X} {P , f} {Q , g} (∧i p⇔q , f≡g) = Σ≡ (propExt p⇔q) (r (propExt p⇔q))
    where
    r : (pq : P ≡ Q) → ≡.subst (λ ○ → ○ → X) pq f ≡ g
    r refl = funExtp λ p → f≡g p p

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

  pull : {X : Set ℓX} → (x y : Lifting ℓP X) → x ≡ y
    → (qy : y .proj₁)
    → x .proj₁ ∧ᵖ λ qx → x .proj₂ qx ≡ y .proj₂ qy
  pull x y refl qy = ∧i qy , refl

  ∙₀ : Atom
  ∙₀ = con DA.∙

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

  -- extData : (γʰ aʰ bʰ : CT)
  --   → (kγ : [ γʰ ] ≡ cʰ)
  --   → (ka : [ aʰ ] ≡ tʰ γʰ)
  --   → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
  --   → (bʰ .proj₁) ∧ᵖ λ pb → [ bʰ .proj₂ pb ]₀ ≡ t̂ (▷₀ (γʰ .proj₂ {!!}) (aʰ .proj₂ (unbox {!tyData γʰ aʰ kγ ka .proj₁!})) ({!ctxData γʰ kγ .proj₂!}) {!tyData γʰ aʰ kγ ka .proj₂!})
  -- extData γʰ aʰ bʰ kγ ka kb with ctxData γʰ kγ | tyData γʰ aʰ kγ ka
  -- ... | pγ , kγ₀ | pa , ka₀ with pull ([ bʰ ]) (tʰ (▷ γʰ aʰ)) kb (∧i tt* , (∧i (unbox pγ) , (∧i (unbox pa) , (∧i (unbox kγ₀) , (∧i (unbox ka₀) , tt*)))))
  -- ... | hb , eqb = box (unbox hb .∧e₂) , box (unbox eqb)

  kk̂ : [ kʰ ] ≡ kʰ
  kk̂ = mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , tt*) λ _ _ → refl

  kĉ : [ cʰ ] ≡ kʰ
  kĉ = mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , tt*) λ _ _ → refl

  kt̂ : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ tʰ γʰ ] ≡ kʰ
  kt̂ γʰ kγ = 
  -- kt̂ : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ tʰ γʰ ] ≡ kʰ
  -- kt̂ γʰ kγ with ctxData γʰ kγ
  -- ... | pγ , kγ₀ =
  --   ≈→≡ (∧i (∧i (λ _ → tt*) , (λ _ → ∧i tt* , (∧i tt* , unbox pγ)))
  --         , (λ _ _ → refl))

  -- k∙ : [ ∙ ] ≡ cʰ
  -- k∙ = ≈→≡ (∧i (∧i (λ _ → tt*) , (λ _ → ∧i tt* , tt*)) , (λ _ _ → refl))

  -- k▷ : (γʰ aʰ : CT) → [ γʰ ] ≡ cʰ → [ aʰ ] ≡ tʰ γʰ → [ ▷ γʰ aʰ ] ≡ cʰ
  -- k▷ γʰ aʰ kγ ka with ctxData γʰ kγ | tyData γʰ aʰ kγ ka
  -- ... | pγ , kγ₀ | pa , ka₀ =
  --   ≈→≡ (∧i pq , pt)
  --   where
  --   pq = ∧i (λ _ → tt*) , (λ _ → ∧i tt* , (∧i (unbox pγ) , (∧i (unbox pa) , (∧i (unbox kγ₀) , (∧i (unbox ka₀) , tt*)))))
  --   pt : ∀ p q → [ ▷ γʰ aʰ ] .proj₂ p ≡ cʰ .proj₂ q
  --   pt _ _ = refl

  -- ku : (γʰ : CT) → [ γʰ ] ≡ cʰ → [ u γʰ ] ≡ tʰ γʰ
  -- ku γʰ kγ =
  --   ≈→≡ (∧i pq , pt)
  --   where
  --   pq = ∧i (λ p → ∧i tt* , (p .∧e₂ .∧e₁))
  --           , (λ q → let pγ = ctxData γʰ kγ .proj₁
  --                    in ∧i tt* , (∧i (unbox pγ) , (∧i (unbox (ctxData γʰ kγ .proj₂)) , tt*)))
  --   pt : ∀ p q → [ u γʰ ] .proj₂ p ≡ tʰ γʰ .proj₂ q
  --   pt p q =
  --     trans (ku₀ (γʰ .proj₂ (p .∧e₂ .∧e₁)) (p .∧e₂ .∧e₂ .∧e₁))
  --           (cong t̂ (congp (γʰ .proj₂)))

  -- kπ : (γʰ aʰ bʰ : CT)
  --   → [ γʰ ] ≡ cʰ
  --   → [ aʰ ] ≡ tʰ γʰ
  --   → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
  --   → [ π γʰ aʰ bʰ ] ≡ tʰ γʰ
  -- kπ γʰ aʰ bʰ kγ ka kb with ctxData γʰ kγ | tyData γʰ aʰ kγ ka | extData γʰ aʰ bʰ kγ ka kb
  -- ... | pγ , kγ₀ | pa , ka₀ | pb , kb₀ =
  --   ≈→≡ (∧i pq , pt)
  --   where
  --   pq : [ π γʰ aʰ bʰ ] .proj₁ ⇔ (tʰ γʰ) .proj₁
  --   pq .∧e₁ p = ∧i tt* , (p .∧e₂ .∧e₁)
  --   pq .∧e₂ q = let wkb = ∧i (unbox kb₀) , tt*
  --                   wka = ∧i (unbox ka₀) , wkb
  --                   wkγ = ∧i (unbox kγ₀) , wka
  --                   wb = ∧i (unbox pb) , wkγ
  --                   wa = ∧i (unbox pa) , wb
  --                   wγ = ∧i (unbox pγ) , wa
  --               in ∧i tt* , wγ
  --   pt : ∀ p q → [ π γʰ aʰ bʰ ] .proj₂ p ≡ tʰ γʰ .proj₂ q
  --   pt p q =
  --     trans (kπ₀ (γʰ .proj₂ (p .∧e₂ .∧e₁))
  --                 (aʰ .proj₂ (p .∧e₂ .∧e₂ .∧e₁))
  --                 (bʰ .proj₂ (p .∧e₂ .∧e₂ .∧e₂ .∧e₁))
  --                 (p .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁)
  --                 (p .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁)
  --                 (p .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁))
  --           (cong t̂ (congp (γʰ .proj₂)))

  -- kσ : (γʰ aʰ bʰ : CT)
  --   → [ γʰ ] ≡ cʰ
  --   → [ aʰ ] ≡ tʰ γʰ
  --   → [ bʰ ] ≡ tʰ (▷ γʰ aʰ)
  --   → [ σ γʰ aʰ bʰ ] ≡ tʰ γʰ
  -- kσ γʰ aʰ bʰ kγ ka kb with ctxData γʰ kγ | tyData γʰ aʰ kγ ka | extData γʰ aʰ bʰ kγ ka kb
  -- ... | pγ , kγ₀ | pa , ka₀ | pb , kb₀ =
  --   ≈→≡ (∧i pq , pt)
  --   where
  --   pq : [ σ γʰ aʰ bʰ ] .proj₁ ⇔ (tʰ γʰ) .proj₁
  --   pq .∧e₁ p = ∧i tt* , (p .∧e₂ .∧e₁)
  --   pq .∧e₂ q = let wkb = ∧i (unbox kb₀) , tt*
  --                   wka = ∧i (unbox ka₀) , wkb
  --                   wkγ = ∧i (unbox kγ₀) , wka
  --                   wb = ∧i (unbox pb) , wkγ
  --                   wa = ∧i (unbox pa) , wb
  --                   wγ = ∧i (unbox pγ) , wa
  --               in ∧i tt* , wγ
  --   pt : ∀ p q → [ σ γʰ aʰ bʰ ] .proj₂ p ≡ tʰ γʰ .proj₂ q
  --   pt p q =
  --     trans (kσ₀ (γʰ .proj₂ (p .∧e₂ .∧e₁))
  --                 (aʰ .proj₂ (p .∧e₂ .∧e₂ .∧e₁))
  --                 (bʰ .proj₂ (p .∧e₂ .∧e₂ .∧e₂ .∧e₁))
  --                 (p .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁)
  --                 (p .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁)
  --                 (p .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₂ .∧e₁))
  --           (cong t̂ (congp (γʰ .proj₂)))

    
