{-# OPTIONS --allow-unsolved-metas #-}
open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Setoid.Quotient
open import QIT.Set.Bijection
open import QIT.QW.Signature

-- Cocontinuous functors preserve colimits: F(colim D) ≅ colim(F ∘ D).
-- This property is crucial for showing that container functors preserve
-- the colimit construction used to build quotient inductive types.
-- The isomorphism enables interchanging functor application and colimit construction.

module QIT.QW.Cocontinuity {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

private
  ℓD = ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

-- Container functor
open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))

-- Size control and staging
open import QIT.Examples.Plump.Postulated S P as Z hiding (rec)
open import QIT.QW.Stage sig
open import QIT.QW.Algebra sig
open import QIT.QW.StageColimit sig

-- Colimits and cocontinuity
open import QIT.QW.Colimit ≤p ℓD ℓD' hiding (_≈ˡ_)

-- Diagram and _∘_ are already in scope from Stage import

private
  ℓc = ℓS ⊔ ℓD
  ℓc' = ℓS ⊔ ℓP ⊔ ℓD ⊔ ℓD'

-- A functor F is cocontinuous if it preserves colimits up to isomorphism.
Cocontinuous : (F : Functor (SetCat (ℓc ⊔ ℓc')) (SetCat (ℓc ⊔ ℓc'))) (D : Diagram/≈ ℓc ℓc')
              → Prop ℓc'
Cocontinuous F D =
  Colim/≈ (F ∘ D) ≅ Functor.ob F (Colim/≈ D)

module ColimF∘D = SetoidQuotient (Colim (F ∘ D))
module ColimD = SetoidQuotient (Colim D)
module Ob = Functor F

module PreservationByPowers
       (depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≡ ιᶻ (t̂ .fst)) (s : S)
       where

  open SetoidQuotient

  rankD₀ : ∀ {α} → D₀ α → Z
  rankD₀ (s , _) = ιᶻ s 

  rankD-cong : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → rankD₀ ŝ ≡ rankD₀ t̂
  rankD-cong {α} {ŝ} {t̂} p = depth-preserving α ŝ t̂ p

  rankD : ∀ {α} → D̃ α /≈ → Z
  rankD {α} = rec (D̃ α) rankD₀ rankD-cong

  rankD-beta : ∀ {α} (ŝ : D₀ α) → rankD (D̃ α ⊢[ ŝ ]) ≡ rankD₀ ŝ
  rankD-beta ŝ = ≡.refl

  rankC : Colim/≈ D → Z
  rankC = rec (Colim D) (λ (_ , ŝ) → rankD ŝ) stable
    where
    stable : ∀ {x y} → Colim D [ x ≈ y ] → rankD (x .proj₂) ≡ rankD (y .proj₂)
    stable (≈lstage i p) = ≡.cong rankD p
    stable (≈lstep {α} {β} p x) =
      -- pweaken does not change the underlying tree (.fst), so both sides
      -- reduce to ιᶻ (s .fst) by the rec-β rewrite; the base case is refl.
      elimp (D̃ α)
            (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
            (λ _ → ≡.refl)
            x
    stable (≈lsym p)     = ≡.sym (stable p)
    stable (≈ltrans p q) = ≡.trans (stable p) (stable q)

  plift : ∀ {α} → (ŝ : D₀ α) → D₀ (rankD₀ ŝ)
  plift (s , _) = s , ≤refl (ιᶻ s)

  s≤rankD : ∀ {α} (ŝ : D₀ α) → ŝ .fst ≤ᵀ rankD (D̃ α ⊢[ ŝ ])
  s≤rankD {α} ŝ = ≤refl (rankD₀ ŝ)

  -- Tree compatibility relation based on ordinal bounds.
  _~ᵀ_ : ∀ (s t : T) → Prop _
  s ~ᵀ t = ιᶻ s ≡ ιᶻ t

  _~ᴰ⁰_ : ∀ {α β} (ŝ : D₀ α) (t̂ : D₀ β) → Prop _
  (s , _) ~ᴰ⁰ (t , _) = s ~ᵀ t

  ~Drefl : ∀ {α} {ŝ : D₀ α} → ŝ ~ᴰ⁰ ŝ
  ~Drefl = ≡.refl
  ~Dsym : ∀ {α β} {ŝ : D₀ α} {t̂ : D₀ β} → ŝ ~ᴰ⁰ t̂ → t̂ ~ᴰ⁰ ŝ
  ~Dsym p = ≡.sym p
  ~Dtrans : ∀ {α β γ} {ŝ : D₀ α} {t̂ : D₀ β} {û : D₀ γ} → ŝ ~ᴰ⁰ t̂ → t̂ ~ᴰ⁰ û → ŝ ~ᴰ⁰ û
  ~Dtrans p q = ≡.trans p q

  _~ᴰ_ : ∀ {α β} (s : D̃ α /≈) (t : D̃ β /≈) → Prop _
  _~ᴰ_ = QuotHetRel∀ D̃ _~ᴰ⁰_

  _~ᴰ'_ : ∀ {α β} (s : D̃ α /≈) (t : D̃ β /≈) → Prop _
  _~ᴰ'_ = QuotHetRel∃ D̃ _~ᴰ⁰_

  ~ᴰ→~ᴰ' : ∀ {α β} (s : D̃ α /≈) (t : D̃ β /≈) → (s ~ᴰ t) → (s ~ᴰ' t)
  ~ᴰ→~ᴰ' = QuotHetRel∀→∃ D̃ _~ᴰ⁰_

  ~ᴰ'→~ᴰ : ∀ {α β} (s : D̃ α /≈) (t : D̃ β /≈) → (s ~ᴰ' t) → (s ~ᴰ t)
  ~ᴰ'→~ᴰ {α} {β} x y ∣ qrwitness x₀ y₀ r ≡.refl ≡.refl ∣ x₀' y₀' px py =
    ~Dtrans (depth-preserving α x₀' x₀ x≈)
      (~Dtrans r
      (depth-preserving β y₀ y₀' y≈))
    where
    s0 = x₀ .fst
    t0 = y₀ .fst
    γ : Z
    γ = α ∨ᶻ β
    δ : Z
    δ = ιᶻ t0
    sw : D₀ γ
    sw = pweaken ∨ᶻ-l x₀
    tw : D₀ γ
    tw = pweaken ∨ᶻ-r y₀
    x≈ : D̃ α [ x₀' ≈ x₀ ]
    x≈ = effectiveness (D̃ α) x₀' x₀ px
    y≈ : D̃ β [ y₀ ≈ y₀' ]
    y≈ = effectiveness (D̃ β) y₀ y₀' (≡.sym py)
    open import QIT.Relation.SetQuotient
    open ≈.≈syntax {S = D̃ δ}
--     u : D̃ (ιᶻ t0) [ subst D₀ {!!} {!!} ≈ {!!} ]
-- --     r = subst D₀ dp (s , ≤refl (ιᶻ s))
-- --           ≈⟨ ≡→≈ (D̃ (ιᶻ t)) (ΣP≡ (subst D₀ dp (s , _)) (s , _) (u dp _)) ⟩
-- --         s , ≡.substp (_≤ ιᶻ t) (≡.sym dp) (≤refl (ιᶻ t))
-- --           ≈⟨ {!!} ⟩
-- --         s , {!!}
-- --           ≈⟨ {!!} ⟩
-- --         t , ≤refl (ιᶻ t) ∎
    

-- -- --   ~ᴰ'→~ᴰ : ∀ {α β} (s : D̃ α /≈) (t : D̃ β /≈) → (s ~ᴰ' t) → (s ~ᴰ t)
-- -- --   ~ᴰ'→~ᴰ {α} {β} s t ∣ v ∣ bx₀ by₀ x₁ x₂ = {!!}
-- -- --     where
-- -- --     f : D₀ α → Σ Z (λ β → D̃ β /≈)
-- -- --     f (s , s≤α) = ιᶻ s , D̃ (ιᶻ s) ⊢[ s , ≤refl _ ]
-- -- --     f-cong : ∀ {ŝ t̂} → D̃ α [ ŝ ≈ t̂ ] → f ŝ ≡ f t̂ 
-- -- --     f-cong {s , s≤α} {t , t≤α} p = ≡.Σ≡ dp q
-- -- --       where
-- -- --       open import QIT.Relation.SetQuotient
-- -- --       open ≈.≈syntax {S = D̃ (ιᶻ t)
-- -- --       dp : ιᶻ s ≡ ιᶻ t
-- -- --       dp = depth-preserving α (s , s≤α) (t , t≤α) p
-- -- --       u : ∀ {β₁ β₂ : Z} (p : β₁ ≡ β₂) (s≤β₁ : s ≤ᵀ β₁)
-- -- --         → fst (subst D₀ p (s , s≤β₁)) ≡ s
-- -- --       u ≡.refl s≤β₁ = ≡.refl
-- -- --       r : D̃ (ιᶻ t) [ subst D₀ dp (s , ≤refl (ιᶻ s)) ≈ (t , ≤refl (ιᶻ t)) ]
-- -- --       r = subst D₀ dp (s , ≤refl (ιᶻ s))
-- -- --             ≈⟨ ≡→≈ (D̃ (ιᶻ t)) (ΣP≡ (subst D₀ dp (s , _)) (s , _) (u dp _)) ⟩
-- -- --           s , ≡.substp (_≤ ιᶻ t) (≡.sym dp) (≤refl (ιᶻ t))
-- -- --             ≈⟨ {!!} ⟩
-- -- --           s , {!!}
-- -- --             ≈⟨ {!!} ⟩
-- -- --           t , ≤refl (ιᶻ t) ∎
-- -- --       q : subst (λ β → D̃ β /≈) dp (D̃ (ιᶻ s) ⊢[ s , ≤refl (ιᶻ s) ])
-- -- --         ≡                         (D̃ (ιᶻ t) ⊢[ t , ≤refl (ιᶻ t) ])
-- -- --       q = quot-drel D₀ (λ {β} → D̃ β [_≈_]) {ιᶻ s} {ιᶻ t} (s , _) (t , _) dp r
-- -- --     d : D̃ α /≈ → Σ Z (λ β → D̃ β /≈)
-- -- --     d = rec (D̃ α) f f-cong

-- -- -- -- --   _~ᴰ_ : ∀ {α β} (s : D̃ α /≈) (t : D̃ β /≈) → Prop _
-- -- -- -- --   _~ᴰ_ {α} {β} ŝ t̂ =
-- -- -- -- --     ∀ (ŝ₀ : D₀ α) (t̂₀ : D₀ β)
-- -- -- -- --     → (ŝ₀ ~ᴰ⁰ t̂₀) ∧ (D̃ α ⊢[ ŝ₀ ] ≡ ŝ) ∧ (D̃ β ⊢[ t̂₀ ] ≡ t̂)

-- -- -- -- --   _~ᶜ⁰_ : (αŝ βt̂ : Colim₀ D) → Prop _
-- -- -- -- --   (α , ŝ) ~ᶜ⁰ (β , t̂) = ŝ ~ᴰ t̂

-- -- -- -- --   _~ᶜ_ : (x y : Colim/≈ D) → Prop _
-- -- -- -- --   x ~ᶜ y = {!∀ (αŝ βt̂ : Colim₀ D) → ? ⊢[ αŝ ] βt̂!}

-- -- -- -- --   ≡→≤ : ∀ {α β} → α ≡ β → α ≤ β
-- -- -- -- --   ≡→≤ ≡.refl = ≤refl _
  
-- -- -- -- --   -- Strong equivalence between trees: ordinal compatibility plus provable equality.
-- -- -- -- --   module ≈s where
-- -- -- -- --     record _≈ˢ_ (s t : T) : Prop (ℓS ⊔ ℓP ⊔ lsuc ℓV ⊔ ℓE) where
-- -- -- -- --       constructor mk≈ˢ
-- -- -- -- --       field
-- -- -- -- --         s~t : s ~ᵀ t
-- -- -- -- --         s≈t : ιᶻ s ⊢ s , ≤refl (ιᶻ s) ≈ᵇ t , ≡→≤ (≡.sym s~t)
-- -- -- -- --     open _≈ˢ_ public
-- -- -- -- --   open ≈s hiding (s~t; s≈t)
  
-- -- -- -- --   ≈srefl : ∀ {s} → s ≈ˢ s
-- -- -- -- --   ≈srefl {s} = mk≈ˢ ≡.refl ≈prefl
  
-- -- -- -- --   ≈ssym : ∀ {s t} → s ≈ˢ t → t ≈ˢ s
-- -- -- -- --   ≈ssym (mk≈ˢ s~ᵀt s≈t) = mk≈ˢ (≡.sym s~ᵀt) (≈psym (≈pweaken (≡→≤ s~ᵀt) s≈t))
  
-- -- -- -- --   ≈strans : ∀ {s t u} → s ≈ˢ t → t ≈ˢ u → s ≈ˢ u
-- -- -- -- --   ≈strans (mk≈ˢ s~ᵀt s≈t) (mk≈ˢ t~ᵀu t≈u) =
-- -- -- -- --     mk≈ˢ (≡.trans s~ᵀt t~ᵀu) (≈ptrans s≈t (≈pweaken (≡→≤ (≡.sym s~ᵀt)) t≈u))
  
-- -- -- -- -- --   ≈scong : ∀ a (f g : ∀ i → T)
-- -- -- -- -- --          → (r : ∀ i → f i ≈ˢ g i)
-- -- -- -- -- --          → W.sup (a , f) ≈ˢ sup (a , g)
-- -- -- -- -- --   ≈scong a f g r = mk≈ˢ (≤≥-cong (ιˢ a) (λ α → ιᶻ (f α)) (λ α → ιᶻ (g α)) λ i → r i .≈s.s~t)
-- -- -- -- -- --                         (≈pcong a (λ α → ιᶻ (f α))
-- -- -- -- -- --                                   (λ i → f i , ≤refl _)
-- -- -- -- -- --                                   (λ i → g i , r i .≈s.s~t .∧.snd)
-- -- -- -- -- --                                   (λ i → r i .≈s.s≈t))

-- -- -- -- -- -- --   plift≈ : ∀ {α} → (ŝ : D̃ α /≈) → D̃ (rankD ŝ) /≈
-- -- -- -- -- -- --   plift≈ {α} = {!!}
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     f : D₀ α → Σ Z (λ β → D̃ β /≈)
-- -- -- -- -- -- --     f (s , s≤α) = ιᶻ s , D̃ (ιᶻ s) ⊢[ s , ≤refl _ ]
-- -- -- -- -- -- --     f-cong : ∀ {ŝ t̂} → D̃ α [ ŝ ≈ t̂ ] → f ŝ ≡ f t̂ 
-- -- -- -- -- -- --     f-cong {s , s≤α} {t , t≤α} p = ≡.Σ≡ dp q
-- -- -- -- -- -- --       where
-- -- -- -- -- -- --       open ≡.≡-Reasoning
-- -- -- -- -- -- --       dp : ιᶻ s ≡ ιᶻ t
-- -- -- -- -- -- --       dp = depth-preserving α (s , s≤α) (t , t≤α) p
-- -- -- -- -- -- --       r : D̃ (ιᶻ s) [ (s , ≤refl (ιᶻ s)) ≈ subst D₀ (≡.sym dp) (t , ≤refl (ιᶻ t)) ]
-- -- -- -- -- -- --       r = {!!}
-- -- -- -- -- -- --       u : ∀ {α β } {ŝ : D₀ β} → (dp : α ≡ β)
-- -- -- -- -- -- --         → subst (λ β → D̃ β /≈) dp (D̃ α ⊢[ subst D₀ (≡.sym dp) ŝ ])
-- -- -- -- -- -- --         ≡ D̃ β ⊢[ ŝ ]
-- -- -- -- -- -- --       u ≡.refl = ≡.refl
-- -- -- -- -- -- --       q : subst (λ β → D̃ β /≈) dp (D̃ (ιᶻ s) ⊢[ s , ≤refl (ιᶻ s) ])
-- -- -- -- -- -- --         ≡                         (D̃ (ιᶻ t) ⊢[ t , ≤refl (ιᶻ t) ])
-- -- -- -- -- -- --       q = begin
-- -- -- -- -- -- --           subst (λ β → D̃ β /≈) dp (D̃ (ιᶻ s) ⊢[ s , _ ])
-- -- -- -- -- -- --             ≡⟨ (≡.cong (subst (λ β → D̃ β /≈) dp) (D̃ (ιᶻ s) ⊢≈[ r ])) ⟩
-- -- -- -- -- -- --           subst (λ β → D̃ β /≈) dp ((D̃ (ιᶻ s) ⊢[ subst D₀ (≡.sym dp) (t , ≤refl (ιᶻ t)) ]))
-- -- -- -- -- -- --             ≡⟨ u dp ⟩
-- -- -- -- -- -- --           D̃ (ιᶻ t) ⊢[ t , ≤refl (ιᶻ t) ] ∎
-- -- -- -- -- -- --     d : D̃ α /≈ → Σ Z (λ β → D̃ β /≈)
-- -- -- -- -- -- --     d = rec (D̃ α) f f-cong

-- -- -- -- -- -- --   isInjHom : ∀ {α β} (p : α ≤ β) → IsInjection (D/≈.hom (box p))
-- -- -- -- -- -- --   isInjHom {α} {β} p {x} {y} q =
-- -- -- -- -- -- --     Dα.elimp₂ {B = λ x y → D/≈.hom (box p) x ≡ D/≈.hom (box p) y → x ≡ y} r x y q
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     module Dα = SetoidQuotient (D̃ α)
-- -- -- -- -- -- --     module Dβ = SetoidQuotient (D̃ β)
-- -- -- -- -- -- --     u : ∀ {x y} → D̃ β [ pweaken p x ≈ pweaken p y ] → D̃ α [ x ≈ y ]
-- -- -- -- -- -- --     u {x} {y} p = {!!}
-- -- -- -- -- -- --     r : (x' y' : D₀ α)
-- -- -- -- -- -- --       → D/≈.hom (box p) (Dα.[ x' ])
-- -- -- -- -- -- --       ≡ D/≈.hom (box p) (Dα.[ y' ])
-- -- -- -- -- -- --       → Dα.[ x' ] ≡ Dα.[ y' ]
-- -- -- -- -- -- --     r x' y' = D/≈.isInjHom p {!!}
  
-- -- -- -- -- -- --   sect : Colim/≈ D → Σ Z D₀
-- -- -- -- -- -- --   sect = rec (Colim D) {!f!} {!!}
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     f : Σ Z (λ α → D̃ α /≈) → Σ Z (λ α → D̃ α /≈)
-- -- -- -- -- -- --     f (α , ŝ) = rankD ŝ , {!!}

-- -- -- -- -- -- --   X = P s
-- -- -- -- -- -- --   D^X : Diagram/≈ ℓc ℓc'
-- -- -- -- -- -- --   D^X = _^_ {ℓc} {ℓc'} D (Lift ℓS X)
-- -- -- -- -- -- --   module D^X = Functor D^X
-- -- -- -- -- -- --   module ColimD^X = SetoidQuotient (Colim D^X)
-- -- -- -- -- -- --   ϕ₀ : Colim₀ D^X → X → Colim₀ D
-- -- -- -- -- -- --   ϕ₀ (α , t̂) x = α , t̂ (lift x)
-- -- -- -- -- -- --   ϕ-cong : ∀ {t̃ ũ} → Colim D^X [ t̃ ≈ ũ ] → (x : X) → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ]
-- -- -- -- -- -- --   ϕ-cong {α , t̂} {α , t̂} (≈lstage α ≡.refl) x = ≡→≈ (Colim D) ≡.refl
-- -- -- -- -- -- --   ϕ-cong {α , t̂} {β , û} (≈lstep p t̂) x = ≈lstep p (t̂ (lift x))
-- -- -- -- -- -- --   ϕ-cong {α , t̂} {β , û} (≈lsym p) x = ≈lsym (ϕ-cong p x)
-- -- -- -- -- -- --   ϕ-cong {α , t̂} {β , û} (≈ltrans p q) x = ≈ltrans (ϕ-cong p x) (ϕ-cong q x)

-- -- -- -- -- -- --   ϕ : Colim/≈ D^X → (X → Colim/≈ D)
-- -- -- -- -- -- --   ϕ f̃ x = ColimD^X.map (Colim D) (λ f → ϕ₀ f x) (λ p → ϕ-cong p x) f̃

-- -- -- -- -- -- --   ϕ-inj≈ : ∀ {t̃ ũ} → (∀ x → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ])
-- -- -- -- -- -- --          → Colim D^X [ t̃ ≈ ũ ]
-- -- -- -- -- -- --   ϕ-inj≈ {α , t̂} {β , û} p = {!!}

-- -- -- -- -- -- --   ϕ-inj : ∀ {t̃ ũ} → (∀ x → ϕ t̃ x ≡ ϕ ũ x) → t̃ ≡ ũ
-- -- -- -- -- -- --   ϕ-inj {t̃} {ũ} = {!!}

-- -- -- -- -- -- --   ϕ-surj≈ : (f : X → Colim/≈ D) → ∃ λ t̃ → ϕ t̃ ≡ f
-- -- -- -- -- -- --   ϕ-surj≈ f = ∣ {!!} , {!!} ∣

-- -- -- -- -- -- --   ϕ-surj : (f : X → Colim/≈ D) → ∃ λ t̃ → ϕ t̃ ≡ f
-- -- -- -- -- -- --   ϕ-surj f = {!!}

-- -- -- -- -- -- --   lemma : Colim/≈ D^X ≅ (X → Colim/≈ D)
-- -- -- -- -- -- --   lemma = Bijection→Iso ϕ ((λ p → ϕ-inj (≡.funExt⁻ p)) , ϕ-surj)

-- -- -- -- -- -- -- -- -- F, D, and F∘D modules are already defined in StageColimit

-- -- -- -- -- -- -- -- F-cong : ∀ {s : S} {f g : P s → Colim₀ D} (p : ∀ i → Colim D [ f i ≈ g i ])
-- -- -- -- -- -- -- --        → (s , f) ≡ (s , g)

-- -- -- -- -- -- -- -- -- Forward direction: map from Colim(F ∘ D) to ob(Colim D).
-- -- -- -- -- -- -- -- -- An element (α, (s, f)) becomes (s, λ i → (α, f i)).
-- -- -- -- -- -- -- -- ϕ : Colim/≈ (F ∘ D) → Ob.ob (Colim/≈ D)
-- -- -- -- -- -- -- -- ϕ = ColimF∘D.quot-rec ϕ₀ ϕ-cong
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   ϕ₀ : Colim₀ (F ∘ D) → Ob.ob (Colim/≈ D)
-- -- -- -- -- -- -- --   ϕ₀ (α , s , f) = s , λ i → ColimD.[ α , f i ]
-- -- -- -- -- -- -- --   ϕ-cong : ∀ {x y} → Colim (F ∘ D) [ x ≈ y ] → ϕ₀ x ≡ ϕ₀ y
-- -- -- -- -- -- -- --   ϕ-cong {α , s , s≤α} {α , t , t≤α} (≈lstage α ≡.refl) = ≡.refl
-- -- -- -- -- -- -- --   ϕ-cong {α , s , s≤α} {β , s , s≤β} (≈lstep p (s , s≤α)) =
-- -- -- -- -- -- -- --     ≡.cong (s ,_) {!≡.cong!}
-- -- -- -- -- -- -- --   ϕ-cong {α , ŝ} {β , t̂} (≈lsym p) = {!!}
-- -- -- -- -- -- -- --   ϕ-cong {α , ŝ} {β , t̂} (≈ltrans p p₁) = {!!}

-- -- -- -- -- -- -- -- --   ϕ-cong-stage : ∀ α {x y} → F∘D.ob α [ x ≈ y ] → Ob.ob (Colim D) [ ϕ₀ (α , x) ≈ ϕ₀ (α , y) ]
-- -- -- -- -- -- -- -- --   ϕ-cong-stage α {a , f} {a , g} (mk≈ꟳ ≡.refl snd≈) =
-- -- -- -- -- -- -- -- --     mk≈ꟳ ≡.refl q
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     q : (i : P a) → Colim D [ α , f i ≈ α , g i ]
-- -- -- -- -- -- -- -- --     q i = ≈lstage α u
-- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- --       u :  α ⊢ f i ≈ᵇ g i
-- -- -- -- -- -- -- -- --       u = snd≈ i

-- -- -- -- -- -- -- -- --   -- Full congruence property for ϕ₀.
-- -- -- -- -- -- -- -- --   ϕ-cong : ∀ {x y} → Colim (F ∘ D) [ x ≈ y ] → Ob.ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
-- -- -- -- -- -- -- -- --   ϕ-cong (≈lstage α e) = ϕ-cong-stage α e
-- -- -- -- -- -- -- -- --   ϕ-cong (≈lstep {α} {j} (sup≤ p) (s , f)) =
-- -- -- -- -- -- -- -- --     mk≈ꟳ ≡.refl λ k → ≈lstep (sup≤ p) (f k)
-- -- -- -- -- -- -- -- --   ϕ-cong (≈lsym p) = ≈fsym (Colim D) (ϕ-cong p)
-- -- -- -- -- -- -- -- --   ϕ-cong (≈ltrans p q) = ≈ftrans (Colim D) (ϕ-cong p) (ϕ-cong q)

-- -- -- -- -- -- -- -- -- -- Congruence for ϕ₀ at a specific stage.

-- -- -- -- -- -- -- -- -- -- -- Backward direction: map from ob(Colim D) to Colim(F ∘ D).
-- -- -- -- -- -- -- -- -- -- -- Find a common upper bound for all stages, then weaken elements to this stage.
-- -- -- -- -- -- -- -- -- -- ψ₀ : ⟨ Ob.ob (Colim D) ⟩ → ⟨ Colim (F ∘ D) ⟩
-- -- -- -- -- -- -- -- -- -- ψ₀ (s , f) = sup (ιˢ s , μ) , s , λ i → pweaken (child≤ (ιˢ s) μ i) (f i .proj₂)
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   μ : P s → Z
-- -- -- -- -- -- -- -- -- --   μ i = f i .proj₁

-- -- -- -- -- -- -- -- -- -- -- Tree compatibility relation based on ordinal bounds.
-- -- -- -- -- -- -- -- -- -- _~ᵀ_ : ∀ (s t : T) → Prop _
-- -- -- -- -- -- -- -- -- -- s ~ᵀ t = ιᶻ s ≤≥ ιᶻ t

-- -- -- -- -- -- -- -- -- -- -- Strong equivalence between trees: ordinal compatibility plus provable equality.
-- -- -- -- -- -- -- -- -- -- module ≈s where
-- -- -- -- -- -- -- -- -- --   record _≈ˢ_ (s t : T) : Prop (ℓS ⊔ ℓP ⊔ lsuc ℓV ⊔ ℓE) where
-- -- -- -- -- -- -- -- -- --     constructor mk≈ˢ
-- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- --       s~t : s ~ᵀ t
-- -- -- -- -- -- -- -- -- --       s≈t : ιᶻ s ⊢ s , ≤refl (ιᶻ s) ≈ᵇ t , s~t .∧.snd
-- -- -- -- -- -- -- -- -- --   open _≈ˢ_ public
-- -- -- -- -- -- -- -- -- -- open ≈s hiding (s~t; s≈t)

-- -- -- -- -- -- -- -- -- -- ≈srefl : ∀ {s} → s ≈ˢ s
-- -- -- -- -- -- -- -- -- -- ≈srefl {s} = mk≈ˢ ≤≥-refl ≈prefl

-- -- -- -- -- -- -- -- -- -- ≈ssym : ∀ {s t} → s ≈ˢ t → t ≈ˢ s
-- -- -- -- -- -- -- -- -- -- ≈ssym (mk≈ˢ s~ᵀt s≈t) = mk≈ˢ (≤≥-sym s~ᵀt) (≈psym (≈pweaken (s~ᵀt .∧.fst) s≈t))

-- -- -- -- -- -- -- -- -- -- ≈strans : ∀ {s t u} → s ≈ˢ t → t ≈ˢ u → s ≈ˢ u
-- -- -- -- -- -- -- -- -- -- ≈strans (mk≈ˢ s~ᵀt s≈t) (mk≈ˢ t~ᵀu t≈u) =
-- -- -- -- -- -- -- -- -- --   mk≈ˢ (≤≥-trans s~ᵀt t~ᵀu) (≈ptrans s≈t (≈pweaken (s~ᵀt .∧.snd) t≈u))

-- -- -- -- -- -- -- -- -- -- ≈scong : ∀ a (f g : ∀ i → T)
-- -- -- -- -- -- -- -- -- --        → (r : ∀ i → f i ≈ˢ g i)
-- -- -- -- -- -- -- -- -- --        → sup (a , f) ≈ˢ sup (a , g)
-- -- -- -- -- -- -- -- -- -- ≈scong a f g r = mk≈ˢ (≤≥-cong (ιˢ a) (λ α → ιᶻ (f α)) (λ α → ιᶻ (g α)) λ i → r i .≈s.s~t)
-- -- -- -- -- -- -- -- -- --                       (≈pcong a (λ α → ιᶻ (f α))
-- -- -- -- -- -- -- -- -- --                                 (λ i → f i , ≤refl _)
-- -- -- -- -- -- -- -- -- --                                 (λ i → g i , r i .≈s.s~t .∧.snd)
-- -- -- -- -- -- -- -- -- --                                 (λ i → r i .≈s.s≈t))

-- -- -- -- -- -- -- -- -- -- -- Under the depth-preserving assumption, we can prove cocontinuity.
-- -- -- -- -- -- -- -- -- -- -- The assumption ensures equivalent elements have compatible ordinal bounds.
-- -- -- -- -- -- -- -- -- -- module _ (depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ŝ .fst ~ᵀ t̂ .fst) where

-- -- -- -- -- -- -- -- -- --   -- Tighten stage-level relations to strong tree equivalences.
-- -- -- -- -- -- -- -- -- --   ≈ᵇ→≈ˢ : ∀ {α ŝ t̂} → D̃ α [ ŝ ≈ t̂ ]
-- -- -- -- -- -- -- -- -- --         → ŝ .fst ≈ˢ t̂ .fst
-- -- -- -- -- -- -- -- -- --   ≈ᵇ→≈ˢ {α} {s , s≤α} {t , t≤α} p = u p
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     u : D̃ α [ s , s≤α ≈ t , t≤α ]
-- -- -- -- -- -- -- -- -- --       → s ≈ˢ t
-- -- -- -- -- -- -- -- -- --     u (≈pcong a μ f g r) = ≈scong a (λ i → f i .fst) (λ i → g i .fst) (λ i → ≈ᵇ→≈ˢ (r i))
-- -- -- -- -- -- -- -- -- --     u (≈psat e ϕ l≤α r≤α) = mk≈ˢ s~ᵀt (≈psat e ϕ (≤refl (ιᶻ (lhs' e ϕ))) _)
-- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- --       s~ᵀt : s ~ᵀ t
-- -- -- -- -- -- -- -- -- --       s~ᵀt = depth-preserving α (s , s≤α) (t , t≤α) p
-- -- -- -- -- -- -- -- -- --     u ≈prefl = ≈srefl
-- -- -- -- -- -- -- -- -- --     u (≈psym p) = ≈ssym (≈ᵇ→≈ˢ p)
-- -- -- -- -- -- -- -- -- --     u (≈ptrans p q) = ≈strans (≈ᵇ→≈ˢ p) (≈ᵇ→≈ˢ q)
-- -- -- -- -- -- -- -- -- --     u (≈pweaken _ p) = (≈ᵇ→≈ˢ p)

-- -- -- -- -- -- -- -- -- --   -- Lift tightening from stage relations to colimit relations.
-- -- -- -- -- -- -- -- -- --   ≈ˡ→≈ˢ : ∀ {ŝ t̂} → Colim D [ ŝ ≈ t̂ ]
-- -- -- -- -- -- -- -- -- --       → ŝ .proj₂ .fst ≈ˢ t̂ .proj₂ .fst
-- -- -- -- -- -- -- -- -- --   ≈ˡ→≈ˢ {α , s , s≤α} {α , t , t≤α} (≈lstage α p) = ≈ᵇ→≈ˢ p
-- -- -- -- -- -- -- -- -- --   ≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈lstep p x) = ≈srefl
-- -- -- -- -- -- -- -- -- --   ≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈lsym p) = ≈ssym (≈ˡ→≈ˢ p)
-- -- -- -- -- -- -- -- -- --   ≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈ltrans p q) = ≈strans (≈ˡ→≈ˢ p) (≈ˡ→≈ˢ q)

-- -- -- -- -- -- -- -- -- --   -- Congruence for ψ₀: convert colimit relations to stage relations.
-- -- -- -- -- -- -- -- -- --   ψ-cong : ∀ {x y} → Ob.ob (Colim D) [ x ≈ y ] → Colim (F ∘ D) [ ψ₀ x ≈ ψ₀ y ]
-- -- -- -- -- -- -- -- -- --   ψ-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = begin
-- -- -- -- -- -- -- -- -- --     ψ₀ (s , f)
-- -- -- -- -- -- -- -- -- --       ≈⟨ ≈lrefl (F ∘ D) ⟩
-- -- -- -- -- -- -- -- -- --     (αf , s , λ i → tf i , _)
-- -- -- -- -- -- -- -- -- --       ≈⟨ ≈lstep ∨ᶻ-l (s , _) ⟩
-- -- -- -- -- -- -- -- -- --     (αf ∨ᶻ αg , s , λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ _) (fi≤μi i)))
-- -- -- -- -- -- -- -- -- --       ≈⟨ ≈lstage (αf ∨ᶻ αg) (mk≈ꟳ ≡.refl v) ⟩
-- -- -- -- -- -- -- -- -- --     (αf ∨ᶻ αg , s , λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ _) (gi≤μi i)))
-- -- -- -- -- -- -- -- -- --       ≈⟨ ≈lsym (≈lstep ∨ᶻ-r (s , _)) ⟩
-- -- -- -- -- -- -- -- -- --     (αg , s , λ i → tg i , _)
-- -- -- -- -- -- -- -- -- --       ≈⟨ ≈lrefl (F ∘ D) ⟩
-- -- -- -- -- -- -- -- -- --     ψ₀ (s , g) ∎
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     μf : P s → Z
-- -- -- -- -- -- -- -- -- --     μf i = f i .proj₁
-- -- -- -- -- -- -- -- -- --     μg : P s → Z
-- -- -- -- -- -- -- -- -- --     μg i = g i .proj₁
-- -- -- -- -- -- -- -- -- --     μ : P s → Z
-- -- -- -- -- -- -- -- -- --     μ i = μf i ∨ᶻ μg i
-- -- -- -- -- -- -- -- -- --     αf = sup (ιˢ s , μf)
-- -- -- -- -- -- -- -- -- --     αg = sup (ιˢ s , μg)
-- -- -- -- -- -- -- -- -- --     α = αf ∨ᶻ αg
-- -- -- -- -- -- -- -- -- --     tf : P s → T
-- -- -- -- -- -- -- -- -- --     tf i = f i .proj₂ .fst
-- -- -- -- -- -- -- -- -- --     tg : P s → T
-- -- -- -- -- -- -- -- -- --     tg i = g i .proj₂ .fst
-- -- -- -- -- -- -- -- -- --     fi≤μi : ∀ i → tf i ≤ᵀ μf i
-- -- -- -- -- -- -- -- -- --     fi≤μi i = f i .proj₂ .snd
-- -- -- -- -- -- -- -- -- --     gi≤μi : ∀ i → tg i ≤ᵀ μg i
-- -- -- -- -- -- -- -- -- --     gi≤μi i = g i .proj₂ .snd
-- -- -- -- -- -- -- -- -- --     v : ∀ i → α ⊢ (tf i  , _) ≈ᵇ (tg i , _)
-- -- -- -- -- -- -- -- -- --     v i = ≈pweaken (≤≤ μi≤α (≤≤ ∨ᶻ-l (fi≤μi i))) (≈ˡ→≈ˢ (snd≈ i) .≈s.s≈t)
-- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- --       μi≤α : μ i ≤ α
-- -- -- -- -- -- -- -- -- --       μi≤α = ∨ᶻ≤ (<≤ ∨ᶻ-l< (child≤ (ιˢ s) μf i)) (<≤ ∨ᶻ-r< (child≤ (ιˢ s) μg i))
-- -- -- -- -- -- -- -- -- --     open ≈.Hom
-- -- -- -- -- -- -- -- -- --     open Setoid (Colim (F ∘ D))
-- -- -- -- -- -- -- -- -- --     open ≈.≈syntax {S = Colim (F ∘ D)}

-- -- -- -- -- -- -- -- -- --   -- Left inverse: ϕ₀ ∘ ψ₀ ≈ id on ob(Colim D).
-- -- -- -- -- -- -- -- -- --   linv : ∀ y → Ob.ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
-- -- -- -- -- -- -- -- -- --   linv (s , g) =
-- -- -- -- -- -- -- -- -- --     ϕ₀ (ψ₀ (s , g))
-- -- -- -- -- -- -- -- -- --       ≈⟨ ≈frefl (Colim D) ⟩
-- -- -- -- -- -- -- -- -- --     (s , λ i → sup (ιˢ s , λ i → g i .proj₁) , pweaken (child≤ (ιˢ s) μ i) (g i .proj₂))
-- -- -- -- -- -- -- -- -- --       ≈⟨ mk≈ꟳ ≡.refl (λ i → ≈lsym (≈lstep (child≤ (ιˢ s) μ i) (g i .proj₂))) ⟩
-- -- -- -- -- -- -- -- -- --     (s , g) ∎
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     μ : P s → Z
-- -- -- -- -- -- -- -- -- --     μ i = g i .proj₁
-- -- -- -- -- -- -- -- -- --     open Setoid (Ob.ob (Colim D))
-- -- -- -- -- -- -- -- -- --     open ≈.≈syntax {S = (Ob.ob (Colim D))}

-- -- -- -- -- -- -- -- -- --   -- Right inverse: ψ₀ ∘ ϕ₀ ≈ id on Colim(F ∘ D).
-- -- -- -- -- -- -- -- -- --   rinv : ∀ x → Colim (F ∘ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
-- -- -- -- -- -- -- -- -- --   rinv (α , (s , g)) = begin
-- -- -- -- -- -- -- -- -- --     ψ₀ (ϕ₀ (α , (s , g)))
-- -- -- -- -- -- -- -- -- --       ≈⟨ refl ⟩
-- -- -- -- -- -- -- -- -- --     α' , (s , λ i → pweaken (child≤ (ιˢ s) (λ _ → α) i) (g i))
-- -- -- -- -- -- -- -- -- --       ≈⟨ (≈lstep ∨ᶻ-r (s , (λ i → pweaken ((child≤ (ιˢ s) (λ _ → α) i)) (g i)))) ⟩
-- -- -- -- -- -- -- -- -- --     α ∨ᶻ α' , (s , λ i → pweaken (≤≤ ∨ᶻ-r (child≤ (ιˢ s) (λ _ → α) i)) (g i))
-- -- -- -- -- -- -- -- -- --       ≈⟨ refl ⟩
-- -- -- -- -- -- -- -- -- --     α ∨ᶻ α' , (s , λ i → pweaken ∨ᶻ-l (g i))
-- -- -- -- -- -- -- -- -- --       ≈⟨ sym (≈lstep ∨ᶻ-l (s , g)) ⟩
-- -- -- -- -- -- -- -- -- --     α , (s , g) ∎
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     α' = sup (ιˢ s , λ _ → α)
-- -- -- -- -- -- -- -- -- --     β = α ∨ᶻ α'
-- -- -- -- -- -- -- -- -- --     open Setoid (Colim (F ∘ D))
-- -- -- -- -- -- -- -- -- --     open ≈.≈syntax {S = Colim (F ∘ D)}

-- -- -- -- -- -- -- -- -- --   -- Main result: container functors are cocontinuous under depth preservation.
-- -- -- -- -- -- -- -- -- --   depthPrserving→cocontinuous : Cocontinuous F D
-- -- -- -- -- -- -- -- -- --   depthPrserving→cocontinuous = ∣ iso ∣
-- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- --     iso : ≈.Iso (Colim (F ∘ D)) (Ob.ob (Colim D))
-- -- -- -- -- -- -- -- -- --     iso = record
-- -- -- -- -- -- -- -- -- --       { ⟦_⟧ = ϕ₀
-- -- -- -- -- -- -- -- -- --       ; ⟦_⟧⁻¹ = ψ₀
-- -- -- -- -- -- -- -- -- --       ; cong = ϕ-cong
-- -- -- -- -- -- -- -- -- --       ; cong⁻¹ = ψ-cong
-- -- -- -- -- -- -- -- -- --       ; linv = linv
-- -- -- -- -- -- -- -- -- --       ; rinv = rinv
-- -- -- -- -- -- -- -- -- --       }
