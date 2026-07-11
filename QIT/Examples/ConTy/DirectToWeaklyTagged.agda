open import QIT.Prelude

module QIT.Examples.ConTy.DirectToWeaklyTagged
  ⦃ pathElim* : PathElim ⦄
  where

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
open import QIT.Types
open import QIT.Maybe
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base

D→W : D.Algebra → W.Algebra
D→W da = {!wa!}
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

  infixl 10 _∷_≟_
  infixl 11 _++_
  data Hyp : Set
  ⟦_⟧ : Hyp → Prop
  data Hyp where
    [] : Hyp
    _∷_≟_ : (hs : Hyp) → (x₁ : ⟦ hs ⟧ → CT) → (x₂ : ⟦ hs ⟧ → CT) → Hyp
  ⟦ [] ⟧ = ⊤
  ⟦ hs ∷ x₁ ≟ x₂ ⟧ = ⟦ hs ⟧ ∧ᵖ λ h* → (x₁ h* ≡ x₂ h*)

  wk∷₁ : {hs : Hyp} {x y : ⟦ hs ⟧ → CT} → (h* : ⟦ hs ∷ x ≟ y ⟧) → (x (h* .∧e₁) ≡ y (h* .∧e₁))
  wk∷₁ (∧i h* , p) = p
  wk∷₂ : {hs : Hyp} {x y : ⟦ hs ⟧ → CT} → ⟦ hs ∷ x ≟ y ⟧ → ⟦ hs ⟧
  wk∷₂ (∧i h* , p) = h*

  _+_ : Hyp → Hyp → Hyp
  wk+₂ : (hs gs : Hyp) → ⟦ hs + gs ⟧ → ⟦ gs ⟧
  wk+₁ : (hs gs : Hyp) → ⟦ hs + gs ⟧ → ⟦ hs ⟧
  hs + [] = hs
  hs + (gs ∷ x ≟ y) =
    hs + gs ∷ (x ∘ᵖ wk+₂ hs gs) ≟ (y ∘ᵖ wk+₂ hs gs)
  wk+₁ hs [] h* = h*
  wk+₁ hs (gs ∷ x ≟ y) (∧i h* , p) = wk+₁ hs gs h*
  wk+₂ hs [] h* = tt
  wk+₂ hs (gs ∷ x ≟ y) (∧i h* , p) = ∧i (wk+₂ hs gs h*) , p
  record CTh : Set where
    constructor _⊢_
    pattern
    field
      hyp : Hyp
      val : ⟦ hyp ⟧ → CT

  open CTh

  ι : CT → CTh
  ι x = [] ⊢ λ _ → x

  cʰ : CTh
  cʰ = [] ⊢ λ _ → ĉ
  kʰ : CTh
  kʰ = [] ⊢ λ _ → k̂
  tʰ : CTh → CTh
  tʰ (hs ⊢ x) = hs ⊢ λ h* → t̂ (x h*)

  [_] : CT → CT
  [ con a ] = ĉ
  [ ty γ a ] = t̂ (con γ)
  [ k̂ ] = k̂
  [ ĉ ] = k̂
  [ t̂ γ ] = k̂
  [ # ] = #

  [_]h : CTh → CTh
  [ hs ⊢ x ]h = hs ⊢ λ h* → [ x h* ]

  getCon₀ : (x : CT) → CT
  getCon₀ (con γ) = #
  getCon₀ (ty γ a) = con γ
  getCon₀ k̂ = #
  getCon₀ ĉ = #
  getCon₀ (t̂ u) = #
  getCon₀ # = #

  getCon : CTh → CTh
  getCon (hs ⊢ x) = hs ⊢ λ h* → getCon₀ (x h*)

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

  ∙ʰ : CTh
  ∙ʰ = ι (con DA.∙)

  ConΣ = ΣP CT λ γ → [ γ ] ≡ ĉ
  ConΣ→Con : ConΣ → DA.Con
  ConΣ→Con (con γ , kγ) = γ
  TyΣ : (γ : ConΣ) → Set
  TyΣ γ = ΣP CT λ a → [ a ] ≡ t̂ (γ .fst)
  TyΣ→Ty : {γ : ConΣ} → TyΣ γ → (DA.Ty (ConΣ→Con γ))
  TyΣ→Ty {con γ , kγ} (ty γ' a , ka) =
    ≡.subst DA.Ty (con-inj (t̂-inj ka)) a

  ▷ʰ : CTh → CTh → CTh
  ▷ʰ (γ-hs ⊢ γ) (a-hs ⊢ a) =
       (γ-hs + a-hs ∷ ((λ h* → getCon₀ (a (wk+₂ γ-hs a-hs h*)))) ≟ (λ h* → γ (wk+₁ γ-hs a-hs h*))
                     ∷ (λ h* → [ a (wk+₂ γ-hs a-hs (h* .∧e₁)) ] ) ≟ (λ h* → t̂ (γ (wk+₁ γ-hs a-hs (h* .∧e₁))))
                     ∷ (λ h* → [ γ (wk+₁ γ-hs a-hs (h* .∧e₁ .∧e₁)) ] ) ≟ λ _ → ĉ)
     ⊢ λ h* → con (ConΣ→Con (γ (wk+₁ γ-hs a-hs (h* .∧e₁ .∧e₁ .∧e₁)) , h* .∧e₂)
               DA.▷ TyΣ→Ty (a (wk+₂ γ-hs a-hs (h* .∧e₁ .∧e₁ .∧e₁)) , h* .∧e₁ .∧e₂))
  k▷ : (γ a : CTh) → [ γ ]h ≡ cʰ → [ a ]h ≡ {!t̂ γ!} → [ ▷ʰ γ a ]h ≡ {!ĉ!}
  -- k▷ (con γ) (ty γ' a) refl refl = refl

  -- u : CT → CT
  -- u (con γ) = ty γ (DA.u γ)
  -- {-# CATCHALL #-}
  -- u _ = #
  -- ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
  -- ku (con γ) refl = refl

  -- π : CT → CT → CT → CT
  -- π (con γ) (ty γ' a) (ty δ b) = ty γ {!!}
  -- -- ty γ (DA.π a' b')
  -- --   where
  -- --   a' : DA.Ty γ
  -- --   a' = {!!}
  -- --   b' : DA.Ty (γ DA.▷ a')
  -- --   b' = {!!}
  -- -- {-# CATCHALL #-}
  -- -- π _ _ _ = #

  -- gt : CT → Maybe DA.Con
  -- gt (con γ) = nothing
  -- gt (ty γ a) = just γ
  -- gt k̂ = nothing
  -- gt ĉ = nothing
  -- gt (t̂ γ) = nothing
  -- gt # = nothing

  -- ĉ→Con : (γ : CT) → [ γ ] ≡ ĉ → DA.Con
  -- ĉ→Con (con γ) _ = γ

  -- v : (γ a : CT)
  --   → (p : [ γ ] ≡ ĉ) → [ a ] ≡ t̂ γ
  --   → [ ▷ʰ γ a ] ≡ ĉ
  --   → gt a ≡ just (ĉ→Con γ p)
  -- v (con γ) (ty γ' a) refl q refl = cong just (con-inj (t̂-inj q))

  -- -- kπ : (γ a b : CT)
  -- --    → [ γ ] ≡ ĉ
  -- --    → [ a ] ≡ t̂ γ
  -- --    → [ b ] ≡ t̂ (▷ γ a)
  -- --    → [ π γ a b ] ≡ t̂ γ
  -- -- kπ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
  -- -- σ : CT → CT → CT → CT
  -- -- σ (con γ) (ty γ' a) (ty δ b) = ty γ' {!!}
  -- -- {-# CATCHALL #-}
  -- -- σ _ _ _ = #
  -- -- kσ : (γ a b : CT)
  -- --    → [ γ ] ≡ ĉ
  -- --    → [ a ] ≡ t̂ γ
  -- --    → [ b ] ≡ t̂ (▷ γ a)
  -- --    → [ σ γ a b ] ≡ t̂ γ
  -- -- kσ (con γ) (ty γ' a) (ty δ b) refl refl refl = refl
  -- -- σ▷ : (γ a b : CT)
  -- --    → [ γ ] ≡ ĉ
  -- --    → [ a ] ≡ t̂ γ
  -- --    → [ b ] ≡ t̂ (▷ γ a)
  -- --    → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
  -- -- σ▷ (con γ) (ty γ' a) (ty δ b) refl refl refl =
  -- --   {!cong (λ b → con (γ DA.▷ a DA.▷ b)) {!!}!}
  -- -- σπ : {!!}


  -- -- -- wa : W.Algebra
  -- -- -- wa = record
  -- -- --   { CT = CTh
  -- -- --   ; [_] = [_]h
  -- -- --   ; k̂ = kʰ
  -- -- --   ; kk̂ = refl
  -- -- --   ; ĉ = cʰ
  -- -- --   ; kĉ = refl
  -- -- --   ; t̂ = tʰ
  -- -- --   ; kt̂ = λ _ _ → {!!}
  -- -- --   ; t̂-γ = {!t̂-γ!}
  -- -- --   ; ∙ = {!con DA.∙!}
  -- -- --   ; k∙ = refl
  -- -- --   -- ; ▷ = ▷
  -- -- --   -- ; k▷ = k▷
  -- -- --   -- ; u = u 
  -- -- --   -- ; ku = ku
  -- -- --   -- ; π = π
  -- -- --   -- ; kπ = kπ
  -- -- --   -- ; σ = σ
  -- -- --   -- ; kσ = kσ
  -- -- --   -- ; σ▷ = σ▷
  -- -- --   -- ; σπ = σπ
  -- -- --   }
