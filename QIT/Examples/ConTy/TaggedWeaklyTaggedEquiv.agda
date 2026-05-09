{-# OPTIONS --allow-unsolved-metas #-}
module QIT.Examples.ConTy.TaggedWeaklyTaggedEquiv where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
import QIT.Examples.ConTy.Tagged as T
import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as WT

T→WT : T.Algebra → WT.Algebra
T→WT ta = record
  { CT = CT
  ; [_] = [_]
  ; k̂ = k̂
  ; kk̂ = kk̂
  ; ĉ = ĉ
  ; kĉ = kĉ
  ; t̂ = {!!}
  ; kt̂ = {!!}
  ; ∙ = {!!}
  ; k∙ = {!!}
  ; ▷ = {!!}
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
  where
  open T.Algebra ta

T→D : T.Algebra → D.Algebra
T→D ta = record
  { Con = Con
  ; Ty = Ty
  ; ∙ = ∙
  ; _▷_ = _▷_
  ; u = u
  ; π = λ {Γ} → π {Γ}
  ; σ = λ {Γ} → σ {Γ}
  ; σ▷ = σ▷
  ; σπ = σπ
  }
  where
  module TA = T.Algebra ta
  open TA using (CT; [_]; ĉ; t̂)
  Con = ΣP TA.CT λ γ → [ γ ] ≡ ĉ
  Ty : Con → Set
  Ty (γ , γp) = ΣP CT λ a → [ a ] ≡ t̂ γ γp
  ∙ : Con
  ∙ = TA.∙ , TA.k∙
  _▷_ : (γ : Con) → Ty γ → Con
  (γ , ky) ▷ (a , ka) = TA.▷ γ ky a ka , TA.k▷ γ ky a ka
  u : ∀ Γ → Ty Γ
  u (γ , ky) = TA.u γ ky , TA.ku γ ky
  π : {Γ : Con} → (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
  π {(γ , ky)} (a , ka) (b , kb) =
    TA.π γ ky a ka b kb , TA.kπ γ ky a ka b kb
  σ : {Γ : Con} → (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
  σ {(γ , ky)} (a , ka) (b , kb) =
    TA.σ γ ky a ka b kb , TA.kσ γ ky a ka b kb
  σ▷ : {γ : Con} {a : Ty γ} {b : Ty (γ ▷ a)} →
      ((γ ▷ a) ▷ b) ≡ (γ ▷ σ {γ} a b)
  σ▷ {γ , kγ} {a , ka} {b , kb} =
    ΣP≡ (((γ , kγ) ▷ (a , ka)) ▷ (b , kb))
        ((γ , kγ) ▷ σ (a , ka) (b , kb))
        (TA.σ▷ γ kγ a ka b kb)
  σπ : {γ : Con} {a : Ty γ} {b : Ty (γ ▷ a)}
       {c : Ty ((γ ▷ a) ▷ b)} →
       π {γ} a (π {γ ▷ a} b c) ≡ π {γ} (σ {γ} a b) (subst Ty σ▷ c)
  σπ {γ , kγ} {a , ka} {b , kb} {c , kc} =
    ΣP≡ (π (a , ka) (π (b , kb) (c , kc))) (π (σ (a , ka) (b , kb)) (subst Ty σ▷ (c , kc)))
        (≡.trans (TA.σπ γ kγ a ka b kb c kc)
                 (≡.dcongsp (TA.π γ kγ (TA.σ γ kγ a ka b kb) (TA.kσ γ kγ a ka b kb))
                            (≡.sym (≡.Jp (λ _ p → fst (subst Ty p (c , kc)) ≡ c) σ▷ ≡.refl))))

D→T : D.Algebra → T.Algebra
D→T da = record
  { CT = CT
  ; [_] = [_]
  ; k̂ = k̂
  ; kk̂ = refl
  ; ĉ = ĉ
  ; kĉ = refl
  ; t̂ = t̂
  ; kt̂ = λ γ kγ → refl
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
  where
  module DA = D.Algebra da
  open DA using (Con; Ty)
  open ≡
  data CT : Set
  [_] : CT → CT
  data CT where
    con : (γ : Con) → CT
    ty : {γ : Con} (a : Ty γ) → CT
    ĉ : CT
    t̂ : (γ : CT) → [ γ ] ≡ ĉ → CT
    k̂ : CT
  [ con γ ] = ĉ
  [ ty {γ} a ] = t̂ (con γ) refl
  [ ĉ ] = k̂
  [ t̂ γ kγ ] = k̂
  [ k̂ ] = k̂

  Con' : Set
  Con' = ΣP CT λ γ → [ γ ] ≡ ĉ
  Ty' : Con' → Set
  Ty' (γ , kγ) = ΣP CT λ a → [ a ] ≡ t̂ γ kγ

  rec : ∀ {X : Set}
    → (rcon : (γ : Con) → X)
    → (rty : {γ : Con} (a : Ty γ) → X)
    → (rĉ : X)
    → (rt̂ : (γ : CT) → [ γ ] ≡ ĉ → X)
    → (rk̂ : X)
    → CT → X
  rec rcon rty rĉ rt̂ rk̂ (con γ) = rcon γ
  rec rcon rty rĉ rt̂ rk̂ (ty a) = rty a
  rec rcon rty rĉ rt̂ rk̂ ĉ = rĉ
  rec rcon rty rĉ rt̂ rk̂ (t̂ γ kγ) = rt̂ γ kγ
  rec rcon rty rĉ rt̂ rk̂ k̂ = rk̂

  -- TODO: Provable, but tedious.
  postulate
    con-inj : ∀ {γ γ'} → con γ ≡ con γ' → γ ≡ γ'
    ty-inj₁ : ∀ {γ γ' a a'} → ty {γ} a ≡ ty {γ'} a' → γ ≡ γ'
    ty-inj₂ : ∀ {γ γ' a a'} → (p : ty {γ} a ≡ ty {γ'} a')
            → subst Ty (ty-inj₁ p) a ≡ a'
    t̂-inj : ∀ {γ γ' kγ kγ'} → (p : t̂ γ kγ ≡ t̂ γ' kγ') → γ ≡ γ'

  Con→Con' : Con → Con'
  Con→Con' γ = con γ , refl
  Con'→Con : Con' → Con
  Con'→Con (con γ , kγ) = γ
  ConIso : Con ↔ Con'
  ConIso = record
    { to = Con→Con'
    ; from = Con'→Con
    ; rinv = λ _ → refl
    ; linv = λ {(con γ , kγ) → refl} }
  
  Ty→Ty' : ∀ {γ} → Ty γ → Ty' (Con→Con' γ)
  Ty→Ty' a = ty a , refl
  Ty'→Ty : ∀ {γ} → Ty' γ → Ty (Con'→Con γ)
  Ty'→Ty {con γ , kγ} (ty a , ka) =
    subst Ty (con-inj (t̂-inj ka)) a

  TyIso : Σ Con Ty ↔ Σ Con' Ty'
  TyIso = record
    { to = λ (γ , a) → Con→Con' γ , Ty→Ty' a
    ; from = λ (γ , a) → Con'→Con γ , Ty'→Ty a
    ; rinv = λ _ → refl
    ; linv = λ (γ , a) → linv γ a }
    where
    linv : (γ : Con') (a : Ty' γ) → (Con→Con' (Con'→Con γ) , Ty→Ty' (Ty'→Ty a)) ≡ (γ , a)
    linv (con γ , kγ) (ty {γ'} a , ka) =
      Σ≡ refl q
      where
      p : γ' ≡ γ
      p = con-inj (t̂-inj ka)
      a' : Ty γ
      a' = subst Ty p a
      r : ty a' ≡ ty a
      r = dcong₂ (λ (γ : Con) (a : Ty γ) → ty {γ} a) (sym p) (subst-inv Ty p)
      q : (ty (subst Ty p a) , _) ≡ (ty a , _)
      q = ΣP≡ (ty (subst Ty (con-inj (t̂-inj ka)) a) , refl)
              (ty a , ka) r
  module ConIso = _↔_ ConIso
  module TyIso = _↔_ TyIso
  

  ce : (P : (γ : CT) (kγ : [ γ ] ≡ ĉ) → Set)
     → (q : ∀ γ → P (con γ) refl)
     → (γ : CT) (kγ : [ γ ] ≡ ĉ)
     → P γ kγ
  ce P q (con γ) _ = q γ
  te : (P : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) (ka : [ a ] ≡ t̂ γ kγ) → Set)
     → (r : ∀ γ a → P (con γ) refl (ty {γ} a) refl)
     → (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
     → P γ kγ a ka
  te P r (con γ) kγ (ty {γ'} a) ka = subst Q q (r γ' a)
    where
    Q : Σ Con' Ty' → Set
    Q ((γ , kγ) , (a , ka)) = P γ kγ a ka
    γ≡γ' : γ ≡ γ'
    γ≡γ' = con-inj (t̂-inj (sym ka))
    p : γ ≡ γ' → subst Ty' _ (ty {γ'} a , refl) ≡ (ty {γ'} a , ka)
    p refl = refl
    q : ((con γ' , refl) , (ty a , refl)) ≡ ((con γ , kγ) , ((ty a) , ka))
    q = Σ≡ (ΣP≡ (con γ' , refl) (con γ , kγ) (t̂-inj ka)) (p γ≡γ')

  ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) → [ a ] ≡ t̂ γ kγ → CT
  ▷ (con γ) kγ (ty {γ'} a) ka = con (γ' DA.▷ a)

  
