{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude

module QIT.Examples.ConTy.TaggedWeaklyTaggedEquiv ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
import QIT.Examples.ConTy.Tagged as T
import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as WT

-- T→WT : T.Algebra → WT.Algebra
-- T→WT ta = record
--   { CT = CT
--   ; [_] = [_]
--   ; k̂ = k̂
--   ; kk̂ = refl
--   ; ĉ = ĉ
--   ; kĉ = refl
--   ; t̂ = t̂'
--   ; kt̂ = kt̂
--   ; ∙ = con (ι TA.∙ , {!!})
--   ; k∙ = {!!}
--   ; ▷ = {!!}
--   ; k▷ = {!!}
--   ; u = {!!}
--   ; ku = {!!}
--   ; π = {!!}
--   ; kπ = {!!}
--   ; σ = {!!}
--   ; kσ = {!!}
--   ; σ▷ = {!!}
--   ; σπ = {!!}
--   }
--   where
--   module TA = T.Algebra ta
--   open ≡
--   data CT : Set
--   [_] : CT → CT
--   Con : Set
--   Ty : Con → Set
--   data CT where
--     con : Con → CT
--     ty : ∀ {γ} → Ty γ → CT
--     ĉ : CT
--     t̂ : (γ : Con) → CT
--     k̂ : CT
--     # : CT -- junk
--   [ con γ ] = ĉ
--   [ ty {γ} a ] = t̂ γ
--   [ ĉ ] = k̂
--   [ t̂ γ ] = k̂
--   [ k̂ ] = k̂
--   [ # ] = #
--   Con = ΣP CT λ γ → [ γ ] ≡ ĉ
--   Ty (γ , kγ) = ΣP CT λ a → [ a ] ≡ t̂ (γ , kγ)
--   -- TODO: Is this constructable? Looks like we need the recursor on TA.
--   ι : TA.CT → CT
--   ι x = {!!}
--   t̂' : CT → CT
--   t̂' (con (γ , kγ)) = t̂ (γ , kγ)
--   t̂' (ty (a , ka)) = #
--   t̂' ĉ = #
--   t̂' (t̂ γ) = #
--   t̂' k̂ = #
--   t̂' # = #
--   kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂' γ ] ≡ k̂
--   kt̂ (con x) kγ = refl

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

  u : (γ : CT) (kγ : [ γ ] ≡ ĉ) → CT
  u γ kγ = ty (DA.u (Con'→Con (γ , kγ)))
  ku : (γ : CT) (kγ : [ γ ] ≡ ĉ) → [ u γ kγ ] ≡ t̂ γ kγ
  ku (con γ) refl = refl

  ▷Σ : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → ΣP CT λ δ → [ δ ] ≡ ĉ
  ▷Σ = te (λ _ _ _ _ → ΣP CT λ δ → [ δ ] ≡ ĉ) λ γ a → con (γ DA.▷ a) , refl

  ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) → [ a ] ≡ t̂ γ kγ → CT
  ▷ γ kγ a ka = (▷Σ γ kγ a ka) .fst

  k▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → [ ▷ γ kγ a ka ] ≡ ĉ
  k▷ γ kγ a ka = (▷Σ γ kγ a ka) .snd

  πΣ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → ΣP CT λ δ → [ δ ] ≡ t̂ γ kγ
  πΣ = te P q
    where
    P : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) (ka : [ a ] ≡ t̂ γ kγ) → Set
    P γ kγ a ka = (b : CT) → [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka)
      → ΣP CT λ δ → [ δ ] ≡ t̂ γ kγ
    q : ∀ γ a → P (con γ) refl (ty a) refl
    q γ a (ty {δ} b) kb = ty (DA.π a (subst Ty (con-inj (t̂-inj kb)) b)) , refl

  π : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → CT
  π γ kγ a ka b kb = (πΣ γ kγ a ka b kb) .fst

  kπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → [ π γ kγ a ka b kb ] ≡ t̂ γ kγ
  kπ γ kγ a ka b kb = (πΣ γ kγ a ka b kb) .snd

  σΣ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → ΣP CT λ δ → [ δ ] ≡ t̂ γ kγ
  σΣ = te P q
    where
    P : (γ : CT) (kγ : [ γ ] ≡ ĉ) (a : CT) (ka : [ a ] ≡ t̂ γ kγ) → Set
    P γ kγ a ka = (b : CT) → [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka)
      → ΣP CT λ δ → [ δ ] ≡ t̂ γ kγ
    q : ∀ γ a → P (con γ) refl (ty a) refl
    q γ a (ty {δ} b) kb = ty (DA.σ a (subst Ty (con-inj (t̂-inj kb)) b)) , refl

  σ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → CT
  σ γ kγ a ka b kb = (σΣ γ kγ a ka b kb) .fst

  kσ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → [ σ γ kγ a ka b kb ] ≡ t̂ γ kγ
  kσ γ kγ a ka b kb = (σΣ γ kγ a ka b kb) .snd

  σ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → ▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb
    ≡ ▷ γ kγ (σ γ kγ a ka b kb) (kσ γ kγ a ka b kb)
  σ▷ (con γ) refl (ty a) refl (ty {δ} b) kb =
    ≡.trans (≡.cong con step₁)
             (≡.cong con (DA.σ▷ {a = a} {b = b'}))
    where
    p : δ ≡ γ DA.▷ a
    p = con-inj (t̂-inj kb)

    b' : Ty (γ DA.▷ a)
    b' = subst Ty p b

    step₁ : δ DA.▷ b ≡ (γ DA.▷ a) DA.▷ b'
    step₁ = ≡.dcong₂ (λ (Γ : Con) (B : Ty Γ) → Γ DA.▷ B) p ≡.refl

  σπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
    → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
    → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
    → (c : CT) (kc : [ c ] ≡ t̂ (▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb)
                               (k▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb))
    → π γ kγ a ka (π (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb c kc)
                  (kπ (▷ γ _ a _) (k▷ γ kγ a ka) b kb c kc)
    ≡ π γ kγ (σ γ kγ a ka b kb) (kσ γ kγ a ka b kb) c
      (≡.trans kc (≡.dcongsp t̂ (σ▷ γ kγ a ka b kb)))
  σπ (con γ) refl (ty a) refl (ty b) refl (ty c) refl = ≡.cong ty DA.σπ


WT→D : WT.Algebra → D.Algebra
WT→D wta = record
  { Con = Con
  ; Ty = Ty
  ; ∙ = {!∙!}
  ; _▷_ = {!_▷_!}
  ; u = {!u!}
  ; π = {!λ {Γ} → π {Γ}!}
  ; σ = {!λ {Γ} → σ {Γ}!}
  ; σ▷ = {!σ▷!}
  ; σπ = {!σπ!}
  }
  where
  module WTA = WT.Algebra wta
  open WTA using (CT; [_]; ĉ; t̂)
  Con = ΣP WTA.CT λ γ → [ γ ] ≡ ĉ
  Ty : Con → Set
  Ty (γ , γp) = ΣP CT λ a → [ a ] ≡ t̂ γ
  -- ∙ : Con
  -- ∙ = WTA.∙ , TA.k∙
  -- _▷_ : (γ : Con) → Ty γ → Con
  -- (γ , ky) ▷ (a , ka) = TA.▷ γ ky a ka , TA.k▷ γ ky a ka
  -- u : ∀ Γ → Ty Γ
  -- u (γ , ky) = TA.u γ ky , TA.ku γ ky
  -- π : {Γ : Con} → (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
  -- π {(γ , ky)} (a , ka) (b , kb) =
  --   TA.π γ ky a ka b kb , TA.kπ γ ky a ka b kb
  -- σ : {Γ : Con} → (A : Ty Γ) (B : Ty (Γ ▷ A)) → Ty Γ
  -- σ {(γ , ky)} (a , ka) (b , kb) =
  --   TA.σ γ ky a ka b kb , TA.kσ γ ky a ka b kb
  -- σ▷ : {γ : Con} {a : Ty γ} {b : Ty (γ ▷ a)} →
  --     ((γ ▷ a) ▷ b) ≡ (γ ▷ σ {γ} a b)
  -- σ▷ {γ , kγ} {a , ka} {b , kb} =
  --   ΣP≡ (((γ , kγ) ▷ (a , ka)) ▷ (b , kb))
  --       ((γ , kγ) ▷ σ (a , ka) (b , kb))
  --       (TA.σ▷ γ kγ a ka b kb)
  -- σπ : {γ : Con} {a : Ty γ} {b : Ty (γ ▷ a)}
  --      {c : Ty ((γ ▷ a) ▷ b)} →
  --      π {γ} a (π {γ ▷ a} b c) ≡ π {γ} (σ {γ} a b) (subst Ty σ▷ c)
  -- σπ {γ , kγ} {a , ka} {b , kb} {c , kc} =
  --   ΣP≡ (π (a , ka) (π (b , kb) (c , kc))) (π (σ (a , ka) (b , kb)) (subst Ty σ▷ (c , kc)))
  --       (≡.trans (TA.σπ γ kγ a ka b kb c kc)
  --                (≡.dcongsp (TA.π γ kγ (TA.σ γ kγ a ka b kb) (TA.kσ γ kγ a ka b kb))
  --                           (≡.sym (≡.Jp (λ _ p → fst (subst Ty p (c , kc)) ≡ c) σ▷ ≡.refl))))

