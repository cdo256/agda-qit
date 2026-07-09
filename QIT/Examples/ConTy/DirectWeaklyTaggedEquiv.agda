open import QIT.Prelude

module QIT.Examples.ConTy.DirectWeaklyTaggedEquiv
  ⦃ pathElim* : PathElim ⦄
  where

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.List
open import QIT.Types
open import QIT.Maybe
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base

D→W : D.Algebra → W.Algebra
D→W da = wa
  where
  open ≡
  module DA = D.Algebra da
  data CT : Set where
    con : DA.Con → CT
    ty : (γ : DA.Con) → DA.Ty γ → CT
    k̂ : CT
    ĉ : CT
    t̂ : CT → CT
    # : CT
  [_] : CT → CT
  [ con a ] = ĉ
  [ ty γ a ] = t̂ (con γ)
  [ k̂ ] = k̂
  [ ĉ ] = k̂
  [ t̂ γ ] = k̂
  [ # ] = #

  con-inj : ∀ {γ δ} → con γ ≡ con δ → γ ≡ δ
  con-inj refl = refl

  ty-inj₁ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ} → ty γ a ≡ ty δ b → γ ≡ δ
  ty-inj₁ refl = refl

  ty-inj₂ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ}
    → (p : ty γ a ≡ ty δ b) → subst DA.Ty (ty-inj₁ p) a ≡ b
  ty-inj₂ refl = refl

  t̂-inj : ∀ {γ δ} → t̂ γ ≡ t̂ δ → γ ≡ δ
  t̂-inj refl = refl

  t̂-γ : (γ a : CT) → [ a ] ≡ t̂ γ → [ γ ] ≡ ĉ
  t̂-γ (con _) _ _ = refl
  t̂-γ (ty _ _) (ty _ _) ()
  t̂-γ k̂ (ty _ _) ()
  t̂-γ ĉ (ty _ _) ()
  t̂-γ (t̂ _) (ty _ _) ()
  t̂-γ # (ty _ _) ()

  ▷ : CT → CT → CT
  ▷ (con γ) (ty γ' a) = con (γ' DA.▷ a)
  {-# CATCHALL #-}
  ▷ _ _ = #
  k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
  k▷ (con γ) (ty γ' a) refl refl = refl

  u : CT → CT
  u (con γ) = ty γ (DA.u γ)
  {-# CATCHALL #-}
  u _ = #
  ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
  ku (con γ) refl = refl

  π : CT → CT → CT → CT
  π (con γ) (ty γ' a) (ty δ b) = {!!}
  -- ty γ (DA.π a' b')
  --   where
  --   a' : DA.Ty γ
  --   a' = {!!}
  --   b' : DA.Ty (γ DA.▷ a')
  --   b' = {!!}
  -- {-# CATCHALL #-}
  -- π _ _ _ = #

  gt : CT → Maybe DA.Con
  gt (con γ) = nothing
  gt (ty γ a) = just γ
  gt k̂ = nothing
  gt ĉ = nothing
  gt (t̂ γ) = nothing
  gt # = nothing

  ĉ→Con : (γ : CT) → [ γ ] ≡ ĉ → DA.Con
  ĉ→Con (con γ) _ = γ

  v : (γ a : CT)
    → (p : [ γ ] ≡ ĉ) → [ a ] ≡ t̂ γ
    → [ ▷ γ a ] ≡ ĉ
    → gt a ≡ just (ĉ→Con γ p)
  v (con γ) (ty γ' a) refl q refl = cong just (con-inj (t̂-inj q))

  kπ : (γ a b : CT)
     → [ γ ] ≡ ĉ
     → [ a ] ≡ t̂ γ
     → [ b ] ≡ t̂ (▷ γ a)
     → [ π γ a b ] ≡ t̂ γ
  kπ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
  σ : CT → CT → CT → CT
  σ (con γ) (ty γ' a) (ty δ b) = ty γ' {!!}
  {-# CATCHALL #-}
  σ _ _ _ = #
  kσ : (γ a b : CT)
     → [ γ ] ≡ ĉ
     → [ a ] ≡ t̂ γ
     → [ b ] ≡ t̂ (▷ γ a)
     → [ σ γ a b ] ≡ t̂ γ
  kσ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
  σ▷ : (γ a b : CT)
     → [ γ ] ≡ ĉ
     → [ a ] ≡ t̂ γ
     → [ b ] ≡ t̂ (▷ γ a)
     → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
  σ▷ (con γ) (ty γ' a) (ty δ b) refl refl refl =
    {!cong (λ b → con (γ DA.▷ a DA.▷ b)) {!!}!}
  σπ : {!!}


  wa : W.Algebra
  wa = record
    { CT = CT
    ; [_] = [_]
    ; k̂ = k̂
    ; kk̂ = refl
    ; ĉ = ĉ
    ; kĉ = refl
    ; t̂ = t̂
    ; kt̂ = λ _ _ → refl
    ; t̂-γ = t̂-γ
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

⟦_⟧ : ∀ {X : Set} → List (X × X) → Prop
⟦ [] ⟧ = ⊤
⟦ (x , y) ∷ hs ⟧ = x ≡ y ∧ ⟦ hs ⟧


D→W' : D.Algebra → W.Algebra
D→W' da = {!wa!}
  where
  open ≡
  module DA = D.Algebra da
  data CT : Set where
    con : DA.Con → CT
    ty : (γ : DA.Con) → DA.Ty γ → CT
    k̂ : CT
    ĉ : CT
    t̂ : CT → CT
    # : CT

  record CTh : Set where
    constructor _⊢_
    pattern
    field
      hyp : List (CT × CT)
      val : ⟦ hyp ⟧ → CT

  tʰ : CTh → CTh
  tʰ (hyp ⊢ x) = hyp ⊢ λ h* → t̂ (x h*)

  ι : CT → CTh
  ι x = [] ⊢ λ _ → x

  [_] : CT → CT
  [ con a ] = ĉ
  [ ty γ a ] = t̂ (con γ)
  [ k̂ ] = k̂
  [ ĉ ] = k̂
  [ t̂ γ ] = k̂
  [ # ] = #

  [_]h : CTh → CTh
  [ hs ⊢ x ]h = hs ⊢ λ h* → [ x h* ]

  con-inj : ∀ {γ δ} → con γ ≡ con δ → γ ≡ δ
  con-inj refl = refl

  ty-inj₁ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ} → ty γ a ≡ ty δ b → γ ≡ δ
  ty-inj₁ refl = refl

  ty-inj₂ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ}
    → (p : ty γ a ≡ ty δ b) → subst DA.Ty (ty-inj₁ p) a ≡ b
  ty-inj₂ refl = refl

  t̂-inj : ∀ {γ δ} → t̂ γ ≡ t̂ δ → γ ≡ δ
  t̂-inj refl = refl

  t̂-γ : (γ a : CT) → [ a ] ≡ t̂ γ → [ γ ] ≡ ĉ
  t̂-γ (con _) _ _ = refl
  t̂-γ (ty _ _) (ty _ _) ()
  t̂-γ k̂ (ty _ _) ()
  t̂-γ ĉ (ty _ _) ()
  t̂-γ (t̂ _) (ty _ _) ()
  t̂-γ # (ty _ _) ()

--   tʰ-γ : (γ a : CTh) → [ a ]h ≡ tʰ γ → [ γ ]h ≡ cʰ
--   tʰ-γ (γ-hs ⊢ γ) (a-hs ⊢ a) ka = let u = t̂-γ γ a in {!!}

--   ∙ : CT
--   ∙ = con DA.∙
--   ∙ʰ : CTh
--   ∙ʰ = ι ∙

--   ▷ : CT → CT → CT
--   ▷ (con γ) (ty γ' a) = con (γ' DA.▷ a)
--   {-# CATCHALL #-}
--   ▷ _ _ = #
--   ▷ʰ : CTh → CTh → CTh
--   ▷ʰ (γ-hs ⊢ con γ) (a-hs ⊢ ty γ' a) = ((con γ , con γ') ∷ γ-hs ++ a-hs) ⊢ {!γ DA.▷ a!}
--   {-# CATCHALL #-}
--   ▷ʰ _ _ = {!!}
--   k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
--   k▷ (con γ) (ty γ' a) refl refl = refl

--   u : CT → CT
--   u (con γ) = ty γ (DA.u γ)
--   {-# CATCHALL #-}
--   u _ = #
--   ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
--   ku (con γ) refl = refl

--   π : CT → CT → CT → CT
--   π (con γ) (ty γ' a) (ty δ b) = ty γ {!!}
--   -- ty γ (DA.π a' b')
--   --   where
--   --   a' : DA.Ty γ
--   --   a' = {!!}
--   --   b' : DA.Ty (γ DA.▷ a')
--   --   b' = {!!}
--   -- {-# CATCHALL #-}
--   -- π _ _ _ = #

--   gt : CT → Maybe DA.Con
--   gt (con γ) = nothing
--   gt (ty γ a) = just γ
--   gt k̂ = nothing
--   gt ĉ = nothing
--   gt (t̂ γ) = nothing
--   gt # = nothing

--   ĉ→Con : (γ : CT) → [ γ ] ≡ ĉ → DA.Con
--   ĉ→Con (con γ) _ = γ

--   v : (γ a : CT)
--     → (p : [ γ ] ≡ ĉ) → [ a ] ≡ t̂ γ
--     → [ ▷ γ a ] ≡ ĉ
--     → gt a ≡ just (ĉ→Con γ p)
--   v (con γ) (ty γ' a) refl q refl = cong just (con-inj (t̂-inj q))

--   kπ : (γ a b : CT)
--      → [ γ ] ≡ ĉ
--      → [ a ] ≡ t̂ γ
--      → [ b ] ≡ t̂ (▷ γ a)
--      → [ π γ a b ] ≡ t̂ γ
--   kπ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
--   σ : CT → CT → CT → CT
--   σ (con γ) (ty γ' a) (ty δ b) = ty γ' {!!}
--   {-# CATCHALL #-}
--   σ _ _ _ = #
--   kσ : (γ a b : CT)
--      → [ γ ] ≡ ĉ
--      → [ a ] ≡ t̂ γ
--      → [ b ] ≡ t̂ (▷ γ a)
--      → [ σ γ a b ] ≡ t̂ γ
--   kσ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
--   σ▷ : (γ a b : CT)
--      → [ γ ] ≡ ĉ
--      → [ a ] ≡ t̂ γ
--      → [ b ] ≡ t̂ (▷ γ a)
--      → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
--   σ▷ (con γ) (ty γ' a) (ty δ b) refl refl refl =
--     {!cong (λ b → con (γ DA.▷ a DA.▷ b)) {!!}!}
--   σπ : {!!}


--   wa : W.Algebra
--   wa = record
--     { CT = CTh
--     ; [_] = [_]h
--     ; k̂ = kʰ
--     ; kk̂ = refl
--     ; ĉ = cʰ
--     ; kĉ = refl
--     ; t̂ = tʰ
--     ; kt̂ = λ _ _ → {!!}
--     ; t̂-γ = {!t̂-γ!}
--     ; ∙ = {!con DA.∙!}
--     ; k∙ = refl
--     -- ; ▷ = ▷
--     -- ; k▷ = k▷
--     -- ; u = u 
--     -- ; ku = ku
--     -- ; π = π
--     -- ; kπ = kπ
--     -- ; σ = σ
--     -- ; kσ = kσ
--     -- ; σ▷ = σ▷
--     -- ; σπ = σπ
--     }

-- W→D : W.Initial → D.Initial
-- W→D (wa , wi) = da , di
--   where
--   open ≡
--   module WA = W.Algebra wa
--   open WA using (CT; [_]; ĉ; t̂)
--   Con : Set
--   Con = ΣP CT λ γ → [ γ ] ≡ ĉ
--   Ty : Con → Set
--   Ty (γ , _) = ΣP CT λ a → [ a ] ≡ t̂ γ
--   Ty-fst : ∀ {γ δ : Con} {a : Ty γ} → (r : γ ≡ δ) → subst Ty r a .fst ≡ a .fst
--   Ty-fst refl = refl
--   ∙ : Con
--   ∙ = WA.∙ , WA.k∙
--   _▷_ : (γ : Con) → Ty γ → Con
--   (γ , kγ) ▷ (a , ka) = WA.▷ γ a , WA.k▷ γ a kγ ka
--   u : (γ : Con) → Ty γ
--   u (γ , kγ) = WA.u γ , WA.ku γ kγ
--   -- Goal: {γ : Con} (a : Ty γ) → Ty (γ ▷ a) → Ty γ
--   π : (γ : Con) (a : Ty γ) → Ty (γ ▷ a) → Ty γ
--   π (γ , kγ) (a , ka) (b , kb) = WA.π γ a b , WA.kπ γ a b kγ ka kb
--   σ : (γ : Con) (a : Ty γ) → Ty (γ ▷ a) → Ty γ
--   σ (γ , kγ) (a , ka) (b , kb) = WA.σ γ a b , WA.kσ γ a b kγ ka kb
--   σ▷ : (γ : Con) (a : Ty γ) (b : Ty (γ ▷ a))
--      → ((γ ▷ a) ▷ b) ≡ (γ ▷ σ γ a b)
--   σ▷ (γ , kγ) (a , ka) (b , kb) =
--     ΣP≡ _ _ (WA.σ▷ γ a b kγ ka kb)
--   σπ : (γ : Con) (a : Ty γ) (b : Ty (γ ▷ a)) (c : Ty ((γ ▷ a) ▷ b))
--      → π γ a (π (γ ▷ a) b c) ≡ π γ (σ γ a b) (subst Ty (σ▷ γ a b) c)
--   σπ (γ , kγ) (a , ka) (b , kb) (c , kc) =
--     ΣP≡ _ _ p
--     where
--     open ≡.≡-Reasoning
--     p : WA.π γ a (WA.π (WA.▷ γ a) b c)
--       ≡ WA.π γ (WA.σ γ a b) (subst Ty (σ▷ (γ , kγ) (a , ka) (b , kb)) (c , kc) .fst)
--     p =
--       WA.π γ a (WA.π (WA.▷ γ a) b c)
--         ≡⟨ WA.σπ γ a b c kγ ka kb kc ⟩
--       WA.π γ (WA.σ γ a b) c
--         ≡⟨ cong (WA.π γ (WA.σ γ a b)) (≡.sym (Ty-fst (σ▷ (γ , kγ) (a , ka) (b , kb)))) ⟩
--       WA.π γ (WA.σ γ a b) (subst Ty (σ▷ (γ , kγ) (a , ka) (b , kb)) (c , _) .fst) ∎

--   da : D.Algebra
--   da = record
--     { Con = Con
--     ; Ty = Ty
--     ; ∙ = ∙
--     ; _▷_ = _▷_ 
--     ; u = u
--     ; π = π
--     ; σ = σ
--     ; σ▷ = σ▷
--     ; σπ = σπ
--     }

--   rec : ∀ (db : D.Algebra) → D.Hom da db
--   rec db = record
--      { conᴿ = conᴿ
--      ; tyᴿ = tyᴿ
--      ; ∙ᴿ = ∙ᴿ
--      ; ▷ᴿ = ▷ᴿ
--      ; uᴿ = uᴿ
--      ; πᴿ = πᴿ
--      ; σᴿ = σᴿ }
--     where
--     conᴿ : D.Con da → D.Con db
--     conᴿ (γ , kγ) = {!!}
--       where
--     tyᴿ : (γ : D.Con da) → D.Ty da γ → D.Ty db (conᴿ γ)
--     ∙ᴿ : conᴿ (D.∙ da) ≡ D.∙ db
--     ▷ᴿ : (γ : D.Con da) (a : D.Ty da γ) →
--           conᴿ ((da D.▷ γ) a) ≡ (db D.▷ conᴿ γ) (tyᴿ γ a)
--     uᴿ : (γ : D.Con da) → tyᴿ γ (D.u da γ) ≡ D.u db (conᴿ γ)
--     πᴿ : (γ : D.Con da) (a : D.Ty da γ) (b : D.Ty da ((da D.▷ γ) a)) →
--           tyᴿ γ (D.π da γ a b) ≡
--           D.π db (conᴿ γ) (tyᴿ γ a)
--           (subst (D.Ty db) _ (tyᴿ ((da D.▷ γ) a) b))
--     σᴿ : (γ : D.Con da) (a : D.Ty da γ) (b : D.Ty da ((da D.▷ γ) a)) →
--           tyᴿ γ (D.σ da γ a b) ≡
--           D.σ db (conᴿ γ) (tyᴿ γ a)
--           (subst (D.Ty db) _ (tyᴿ ((da D.▷ γ) a) b))
--     module db = D.Algebra db
    

--   di : isInitial D.Cat da
--   di = {!!}
--   -- di db f g = D.mk≈ Con≡ Ty≡
--   --   where
--   --   module db = D.Algebra db
--   --   module f = D.Hom f
--   --   module g = D.Hom g
--   --   Con≡ : ∀ (γ : Con) → f.conᴿ γ ≡ g.conᴿ γ
--   --   Con≡ (γ , kγ) = {!!}
--   --   Ty≡ : (γ : Con) (a : Ty γ) → subst db.Ty (Con≡ γ) (f.tyᴿ γ a) ≡ g.tyᴿ γ a

D→W'' : D.Algebra → W.Algebra
D→W'' da = {!wa!}
  where
  open ≡
  module DA = D.Algebra da
  data CT : Set where
    con : DA.Con → CT
    ty : (γ : DA.Con) → DA.Ty γ → CT
    k̂ : CT
    ĉ : CT
    t̂ : CT → CT
    # : CT
  [_] : CT → CT
  [ con a ] = ĉ
  [ ty γ a ] = t̂ (con γ)
  [ k̂ ] = k̂
  [ ĉ ] = k̂
  [ t̂ γ ] = k̂
  [ # ] = #

  con-inj : ∀ {γ δ} → con γ ≡ con δ → γ ≡ δ
  con-inj refl = refl

  ty-inj₁ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ} → ty γ a ≡ ty δ b → γ ≡ δ
  ty-inj₁ refl = refl

  ty-inj₂ : ∀ {γ δ} {a : DA.Ty γ} {b : DA.Ty δ}
    → (p : ty γ a ≡ ty δ b) → subst DA.Ty (ty-inj₁ p) a ≡ b
  ty-inj₂ refl = refl

  t̂-inj : ∀ {γ δ} → t̂ γ ≡ t̂ δ → γ ≡ δ
  t̂-inj refl = refl

  t̂-γ : (γ a : CT) → [ a ] ≡ t̂ γ → [ γ ] ≡ ĉ
  t̂-γ (con _) _ _ = refl
  t̂-γ (ty _ _) (ty _ _) ()
  t̂-γ k̂ (ty _ _) ()
  t̂-γ ĉ (ty _ _) ()
  t̂-γ (t̂ _) (ty _ _) ()
  t̂-γ # (ty _ _) ()

  ▷ : CT → CT → CT
  ▷ (con γ) (ty γ' a) = con (γ' DA.▷ a)
  {-# CATCHALL #-}
  ▷ _ _ = #
  k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
  k▷ (con γ) (ty γ' a) refl refl = refl

  u : CT → CT
  u (con γ) = ty γ (DA.u γ)
  {-# CATCHALL #-}
  u _ = #
  ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
  ku (con γ) refl = refl

  π : CT → CT → CT → CT
  π (con γ) (ty γ' a) (ty δ b) = {!!}

  gt : CT → Maybe DA.Con
  gt (con γ) = nothing
  gt (ty γ a) = just γ
  gt k̂ = nothing
  gt ĉ = nothing
  gt (t̂ γ) = nothing
  gt # = nothing

  ĉ→Con : (γ : CT) → [ γ ] ≡ ĉ → DA.Con
  ĉ→Con (con γ) _ = γ

  v : (γ a : CT)
    → (p : [ γ ] ≡ ĉ) → [ a ] ≡ t̂ γ
    → [ ▷ γ a ] ≡ ĉ
    → gt a ≡ just (ĉ→Con γ p)
  v (con γ) (ty γ' a) refl q refl = cong just (con-inj (t̂-inj q))

  kπ : (γ a b : CT)
     → [ γ ] ≡ ĉ
     → [ a ] ≡ t̂ γ
     → [ b ] ≡ t̂ (▷ γ a)
     → [ π γ a b ] ≡ t̂ γ
  kπ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
  σ : CT → CT → CT → CT
  σ (con γ) (ty γ' a) (ty δ b) = ty γ' {!!}
  {-# CATCHALL #-}
  σ _ _ _ = #
  kσ : (γ a b : CT)
     → [ γ ] ≡ ĉ
     → [ a ] ≡ t̂ γ
     → [ b ] ≡ t̂ (▷ γ a)
     → [ σ γ a b ] ≡ t̂ γ
  kσ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
  σ▷ : (γ a b : CT)
     → [ γ ] ≡ ĉ
     → [ a ] ≡ t̂ γ
     → [ b ] ≡ t̂ (▷ γ a)
     → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
  σ▷ (con γ) (ty γ' a) (ty δ b) refl refl refl =
    {!cong (λ b → con (γ DA.▷ a DA.▷ b)) {!!}!}
  σπ : {!!}


  wa : W.Algebra
  wa = record
    { CT = CT
    ; [_] = [_]
    ; k̂ = k̂
    ; kk̂ = refl
    ; ĉ = ĉ
    ; kĉ = refl
    ; t̂ = t̂
    ; kt̂ = λ _ _ → refl
    ; t̂-γ = t̂-γ
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
