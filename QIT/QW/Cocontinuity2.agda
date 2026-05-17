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

module QIT.QW.Cocontinuity2 {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

private
  ℓD = ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

open import QIT.Container.Base
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))

open import QIT.Examples.Plump.Postulated S P as Z hiding (rec)
open import QIT.QW.Stage sig
open import QIT.QW.Algebra sig
open import QIT.QW.StageColimit sig
open import QIT.QW.Colimit ≤p ℓD ℓD' hiding (_≈ˡ_)

private
  ℓc = ℓS ⊔ ℓD
  ℓc' = ℓS ⊔ ℓP ⊔ ℓD ⊔ ℓD'

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
  rankD₀ (t , _) = ιᶻ t

  rankD-cong : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → rankD₀ ŝ ≡ rankD₀ t̂
  rankD-cong {α} {ŝ} {t̂} p = depth-preserving α ŝ t̂ p

  rankD : ∀ {α} → D̃ α /≈ → Z
  rankD {α} = rec (D̃ α) rankD₀ rankD-cong

  rankD-beta : ∀ {α} (t̂ : D₀ α) → rankD (D̃ α ⊢[ t̂ ]) ≡ rankD₀ t̂
  rankD-beta t̂ = ≡.refl

  rankC : Colim/≈ D → Z
  rankC = rec (Colim D) (λ (_ , t̂) → rankD t̂) stable
    where
    stable : ∀ {x y} → Colim D [ x ≈ y ] → rankD (x .proj₂) ≡ rankD (y .proj₂)
    stable (≈lstage i p) = ≡.cong rankD p
    stable (≈lstep {α} {β} p x) =
      elimp (D̃ α)
            (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
            (λ _ → ≡.refl)
            x
    stable (≈lsym p) = ≡.sym (stable p)
    stable (≈ltrans p q) = ≡.trans (stable p) (stable q)

  plift : ∀ {α} → (t̂ : D₀ α) → D₀ (rankD₀ t̂)
  plift (t , _) = t , ≤refl (ιᶻ t)

  plift≈ : ∀ {α} → (t̂ : D̃ α /≈) → D̃ (rankD t̂) /≈
  plift≈ {α} t̂ = subst (λ β → D̃ β /≈) (first t̂) ((d t̂) .proj₂)
    where
    module Dα = SetoidQuotient (D̃ α)
    open ≡.≡-Reasoning

    same-fst : ∀ {γ} {t : T} (p q : t ≤ᵀ γ) → D̃ γ [ (t , p) ≈ (t , q) ]
    same-fst p q = ≡→≈ (D̃ _) (ΣP≡ (_ , p) (_ , q) ≡.refl)

    castʳ : ∀ {γ} {x y z : D₀ γ} → y ≡ z → D̃ γ [ x ≈ y ] → D̃ γ [ x ≈ z ]
    castʳ ≡.refl p = p

    castˡ : ∀ {γ} {x y z : D₀ γ} → x ≡ y → D̃ γ [ x ≈ z ] → D̃ γ [ y ≈ z ]
    castˡ ≡.refl p = p

    cast-rhs : ∀ {γ s t} {ps : s ≤ᵀ γ} {pt qt : t ≤ᵀ γ}
      → D̃ γ [ (s , ps) ≈ (t , pt) ]
      → D̃ γ [ (s , ps) ≈ (t , qt) ]
    cast-rhs {pt = pt} {qt = qt} p = ≈ptrans p (same-fst pt qt)

    transport≈ : ∀ {γ δ} (p : γ ≡ δ) {x y : D₀ γ}
      → D̃ γ [ x ≈ y ] → D̃ δ [ subst D₀ p x ≈ subst D₀ p y ]
    transport≈ ≡.refl r = r

    subst-D₀-fst : ∀ {γ δ} (p : γ ≡ δ) (û : D₀ γ) → (subst D₀ p û) .fst ≡ û .fst
    subst-D₀-fst ≡.refl û = ≡.refl

    plift-fst : ∀ {γ} (û : D₀ γ) → (plift û) .fst ≡ û .fst
    plift-fst û = ≡.refl

    plift-psup : ∀ a μ (f : ∀ i → D₀ (μ i))
      → plift (psup a μ f) ≡ psup a (λ i → rankD₀ (f i)) (λ i → plift (f i))
    plift-psup a μ f = ΣP≡ _ _ (≡.refl)

    exactify : ∀ {γ} {ŝ t̂ : D₀ γ} (p : D̃ γ [ ŝ ≈ t̂ ])
      → D̃ (rankD₀ ŝ) [ plift ŝ ≈ subst D₀ (≡.sym (rankD-cong p)) (plift t̂) ]
    exactify (≈pcong a μ f₁ g r) = castˡ (plift-psup a μ f₁) (castʳ rhs≈ base)
      where
      δi : ∀ i → rankD₀ (f₁ i) ≡ rankD₀ (g i)
      δi i = rankD-cong (r i)
      μ' : P a → Z
      μ' i = rankD₀ (f₁ i)
      f' : ∀ i → D₀ (μ' i)
      f' i = plift (f₁ i)
      g' : ∀ i → D₀ (μ' i)
      g' i = subst D₀ (≡.sym (δi i)) (plift (g i))
      base : D̃ (rankD₀ (psup a μ f₁)) [ psup a μ' f' ≈ psup a μ' g' ]
      base = ≈pcong a μ' f' g' (λ i → exactify (r i))
      dp : rankD₀ (psup a μ f₁) ≡ rankD₀ (psup a μ g)
      dp = rankD-cong (≈pcong a μ f₁ g r)
      g'fst : ∀ i → (g' i) .fst ≡ (plift (g i)) .fst
      g'fst i = subst-D₀-fst (≡.sym (δi i)) (plift (g i))
      rhs≈ : psup a μ' g' ≡ subst D₀ (≡.sym dp) (plift (psup a μ g))
      rhs≈ = ΣP≡ _ _ rhsfst
        where
        rhsfst : (psup a μ' g') .fst ≡ (subst D₀ (≡.sym dp) (plift (psup a μ g))) .fst
        rhsfst = ≡.trans (≡.cong (λ h → W.sup (a , h)) (≡.funExt g'fst))
                          (≡.sym (subst-D₀-fst (≡.sym dp) (plift (psup a μ g))))
    exactify (≈psat e ϕ l≤α r≤α) = castʳ rhs≈ base
      where
      dp : rankD₀ (lhs' e ϕ , l≤α) ≡ rankD₀ (rhs' e ϕ , r≤α)
      dp = rankD-cong (≈psat e ϕ l≤α r≤α)
      base : D̃ (rankD₀ (lhs' e ϕ , l≤α)) [ plift (lhs' e ϕ , l≤α) ≈ (rhs' e ϕ , ≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _)) ]
      base = ≈psat e ϕ (≤refl _) (≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _))
      rhs≈ : (rhs' e ϕ , ≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _)) ≡ subst D₀ (≡.sym dp) (plift (rhs' e ϕ , r≤α))
      rhs≈ = ΣP≡ _ _ (≡.sym (subst-D₀-fst (≡.sym dp) (plift (rhs' e ϕ , r≤α))))
    exactify ≈prefl = ≈prefl
    exactify {ŝ = ŝ} {t̂ = t̂} (≈psym p) =
      castˡ {z = subst D₀ dp (plift t̂)} lhs≈ (transport≈ dp (≈psym (exactify p)))
      where
      dp : rankD₀ t̂ ≡ rankD₀ ŝ
      dp = rankD-cong p
      lhs≈ : subst D₀ dp (subst D₀ (≡.sym dp) (plift ŝ)) ≡ plift ŝ
      lhs≈ = ≡.subst-inv D₀ (≡.sym dp)
    exactify {ŝ = ŝ} {t̂ = û} (≈ptrans {ŝ = ŝ} {t̂ = t̂} {û = û} p q) = castʳ rhs≈ (≈ptrans (exactify p) mid)
      where
      dp : rankD₀ ŝ ≡ rankD₀ t̂
      dp = rankD-cong p
      dq : rankD₀ t̂ ≡ rankD₀ û
      dq = rankD-cong q
      mid : D̃ (rankD₀ ŝ) [ subst D₀ (≡.sym dp) (plift t̂) ≈ subst D₀ (≡.sym dp) (subst D₀ (≡.sym dq) (plift û)) ]
      mid = transport≈ (≡.sym dp) (exactify q)
      rhs≈ : subst D₀ (≡.sym dp) (subst D₀ (≡.sym dq) (plift û)) ≡ subst D₀ (≡.sym (rankD-cong (≈ptrans p q))) (plift û)
      rhs≈ = ≡.subst-subst {P = D₀} (≡.sym dq) {y≡z = ≡.sym dp} {p = plift û}
    exactify (≈pweaken α≤β p) = exactify p

    f : D₀ α → Σ Z (λ β → D̃ β /≈)
    f t̂ = rankD₀ t̂ , D̃ (rankD₀ t̂) ⊢[ plift t̂ ]

    u : ∀ {γ δ} {û : D₀ δ} (p : γ ≡ δ)
      → subst (λ β → D̃ β /≈) p (D̃ γ ⊢[ subst D₀ (≡.sym p) û ])
      ≡ D̃ δ ⊢[ û ]
    u ≡.refl = ≡.refl

    f-cong : ∀ {ŝ t̂ : D₀ α} → (p : D̃ α [ ŝ ≈ t̂ ]) → f ŝ ≡ f t̂
    f-cong {ŝ} {t̂} p = ≡.Σ≡ dp q
      where
      dp : rankD₀ ŝ ≡ rankD₀ t̂
      dp = rankD-cong p
      q : subst (λ β → D̃ β /≈) dp (D̃ (rankD₀ ŝ) ⊢[ plift ŝ ])
        ≡ D̃ (rankD₀ t̂) ⊢[ plift t̂ ]
      q = begin
          subst (λ β → D̃ β /≈) dp (D̃ (rankD₀ ŝ) ⊢[ plift ŝ ])
            ≡⟨ ≡.cong (subst (λ β → D̃ β /≈) dp) (D̃ (rankD₀ ŝ) ⊢≈[ exactify p ]) ⟩
          subst (λ β → D̃ β /≈) dp (D̃ (rankD₀ ŝ) ⊢[ subst D₀ (≡.sym dp) (plift t̂) ])
            ≡⟨ u dp ⟩
          D̃ (rankD₀ t̂) ⊢[ plift t̂ ] ∎

    d : D̃ α /≈ → Σ Z (λ β → D̃ β /≈)
    d = rec (D̃ α) f f-cong

    first : ∀ t̂ → (d t̂) .proj₁ ≡ rankD t̂
    first = elimp (D̃ α) (λ t̂ → (d t̂) .proj₁ ≡ rankD t̂) (λ _ → ≡.refl)

  s≤rankD : ∀ {α} (t̂ : D₀ α) → t̂ .fst ≤ᵀ rankD (D̃ α ⊢[ t̂ ])
  s≤rankD {α} t̂ = ≤refl (rankD₀ t̂)

  _~ᵀ_ : ∀ (s t : T) → Prop _
  s ~ᵀ t = ιᶻ s ≡ ιᶻ t

  _~⁰_ : ∀ {α β} → D₀ α → D₀ β → Prop _
  (s , _) ~⁰ (t , _) = s ~ᵀ t

  _~∀_ : ∀ {α β} → D̃ α /≈ → D̃ β /≈ → Prop _
  _~∀_ = QuotHetRel∀ D̃ _~⁰_

  _~∃_ : ∀ {α β} → D̃ α /≈ → D̃ β /≈ → Prop _
  _~∃_ = QuotHetRel∃ D̃ _~⁰_

  ~∀→∃ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → ŝ ~∀ t̂ → ŝ ~∃ t̂
  ~∀→∃ = QuotHetRel∀→∃ D̃ _~⁰_

  ~∃→∀ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → ŝ ~∃ t̂ → ŝ ~∀ t̂
  ~∃→∀ {α} {β} ŝ t̂ ∣ qrwitness (s' , s'≤α) (t' , t'≤β) r ps' pt' ∣ (s , s≤α) (t , t≤β) ps pt = p
    where
    module Dα = SetoidQuotient (D̃ α)
    module Dβ = SetoidQuotient (D̃ β)

    rs : D̃ α [ (s , s≤α) ≈ (s' , s'≤α) ]
    rs = Dα.effectiveness _ _ (≡.trans ps (≡.sym ps'))

    rt : D̃ β [ (t' , t'≤β) ≈ (t , t≤β) ]
    rt = Dβ.effectiveness _ _ (≡.trans pt' (≡.sym pt))

    qs : s ~ᵀ s'
    qs = depth-preserving α (s , s≤α) (s' , s'≤α) rs

    qt : t' ~ᵀ t
    qt = depth-preserving β (t' , t'≤β) (t , t≤β) rt

    p : (s , s≤α) ~⁰ (t , t≤β)
    p = ≡.trans qs (≡.trans r qt)

  ~⇔ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → (ŝ ~∀ t̂) ⇔ (ŝ ~∃ t̂)
  ~⇔ ŝ t̂ = ~∀→∃ ŝ t̂ , ~∃→∀ ŝ t̂

  _~ᶜ⁰_ : Colim₀ D → Colim₀ D → Prop _
  (α , ŝ) ~ᶜ⁰ (β , t̂) = ŝ ~∀ t̂

  _~ᶜ∃⁰_ : Colim₀ D → Colim₀ D → Prop _
  (α , ŝ) ~ᶜ∃⁰ (β , t̂) = ŝ ~∃ t̂

  _~ᶜ∀_ : Colim/≈ D → Colim/≈ D → Prop _
  _~ᶜ∀_ = QuotHomRel∀ (Colim D) _~ᶜ⁰_

  _~ᶜ∃_ : Colim/≈ D → Colim/≈ D → Prop _
  _~ᶜ∃_ = QuotHomRel∃ (Colim D) _~ᶜ⁰_

  ~ᶜ∀→∃ : ∀ (x y : Colim/≈ D) → x ~ᶜ∀ y → x ~ᶜ∃ y
  ~ᶜ∀→∃ = QuotHomRel∀→∃ (Colim D) _~ᶜ⁰_

  ~ᶜ∃→∀ : ∀ (x y : Colim/≈ D) → x ~ᶜ∃ y → x ~ᶜ∀ y
  ~ᶜ∃→∀ x y ∣ qrwitness x₀ y₀ r px py ∣ x₁ y₁ qx qy =
    {!!}

  ~ᶜ⇔ : ∀ (x y : Colim/≈ D) → (x ~ᶜ∀ y) ⇔ (x ~ᶜ∃ y)
  ~ᶜ⇔ x y = ~ᶜ∀→∃ x y , ~ᶜ∃→∀ x y

  X = P s
  D^X : Diagram/≈ ℓc ℓc'
  D^X = _^_ {ℓc} {ℓc'} D (Lift ℓS X)
  module D^X = Functor D^X
  module ColimD^X = SetoidQuotient (Colim D^X)

  ϕ₀ : Colim₀ D^X → X → Colim₀ D
  ϕ₀ (α , t̂) x = α , t̂ (lift x)

  ϕ-cong : ∀ {t̃ ũ} → Colim D^X [ t̃ ≈ ũ ] → (x : X) → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ]
  ϕ-cong {α , t̂} {α , t̂} (≈lstage α ≡.refl) x = ≡→≈ (Colim D) ≡.refl
  ϕ-cong {α , t̂} {β , û} (≈lstep p t̂) x = ≈lstep p (t̂ (lift x))
  ϕ-cong {α , t̂} {β , û} (≈lsym p) x = ≈lsym (ϕ-cong p x)
  ϕ-cong {α , t̂} {β , û} (≈ltrans p q) x = ≈ltrans (ϕ-cong p x) (ϕ-cong q x)

  ϕ : Colim/≈ D^X → (X → Colim/≈ D)
  ϕ f̃ x = ColimD^X.map (Colim D) (λ f → ϕ₀ f x) (λ p → ϕ-cong p x) f̃

  join≈ : ∀ {i j} {x : D̃ i /≈} {y : D̃ j /≈}
        → Colim D [ i , x ≈ j , y ]
        → ∀ {γ} (i≤γ : i ≤ γ) (j≤γ : j ≤ γ)
        → D.hom (box i≤γ) x ≡ D.hom (box j≤γ) y
  join≈ = recˡ D J c-stage c-step c-sym c-trans
    where
    open ≡.≡-Reasoning

    J : ∀ {s t} → Colim D [ s ≈ t ] → Prop _
    J {s} {t} _ = ∀ {γ} (s≤γ : s .proj₁ ≤ γ) (t≤γ : t .proj₁ ≤ γ)
      → D.hom (box s≤γ) (s .proj₂) ≡ D.hom (box t≤γ) (t .proj₂)

    c-stage : ∀ i {x x'} (e : x ≡ x') → ∀ {γ} (i≤γ : i ≤ γ) (i≤γ' : i ≤ γ)
      → D.hom (box i≤γ) x ≡ D.hom (box i≤γ') x'
    c-stage i {x} {x'} e {γ} i≤γ i≤γ' = begin
      D.hom (box i≤γ) x
        ≡⟨ resp≤ ⟩
      D.hom (box i≤γ') x
        ≡⟨ ≡.cong (D.hom (box i≤γ')) e ⟩
      D.hom (box i≤γ') x' ∎
      where
      resp≤ : D.hom (box i≤γ) x ≡ D.hom (box i≤γ') x
      resp≤ = D.resp {f = box i≤γ} {g = box i≤γ'} (≡.isPropBox _ _) {x = x}

    c-step : ∀ {i j} (p : i ≤ j) (x : D̃ i /≈) → ∀ {γ} (i≤γ : i ≤ γ) (j≤γ : j ≤ γ)
      → D.hom (box i≤γ) x ≡ D.hom (box j≤γ) (D.hom (box p) x)
    c-step {i} {j} p x {γ} i≤γ j≤γ = begin
      D.hom (box i≤γ) x
        ≡⟨ resp≤ ⟩
      D.hom (box (≤≤ j≤γ p)) x
        ≡⟨ comp≤ ⟩
      D.hom (box j≤γ) (D.hom (box p) x) ∎
      where
      resp≤ : D.hom (box i≤γ) x ≡ D.hom (box (≤≤ j≤γ p)) x
      resp≤ = D.resp {f = box i≤γ} {g = box (≤≤ j≤γ p)} (≡.isPropBox _ _) {x = x}

      comp≤ : D.hom (box (≤≤ j≤γ p)) x ≡ D.hom (box j≤γ) (D.hom (box p) x)
      comp≤ = D.comp (box p) (box j≤γ) {x = x}

    c-sym : ∀ {s t} (r : Colim D [ s ≈ t ]) → J r → J (≈lsym r)
    c-sym {s} {t} r ih t≤γ s≤γ = ≡.sym (ih s≤γ t≤γ)

    ≡→≤ : ∀ {α β} → α ≡ β → α ≤ β
    ≡→≤ {α} {α} ≡.refl = ≤refl α

    c-trans : ∀ {s t u} (r₁ : Colim D [ s ≈ t ]) (r₂ : Colim D [ t ≈ u ])
      → J r₁ → J r₂ → J (≈ltrans r₁ r₂)
    c-trans {s = s} {t} {u} r₁ r₂ ih₁ ih₂ {γ} s≤γ u≤γ = ≡.trans (ih₁ s≤γ t≤γ) (ih₂ t≤γ u≤γ)
      where
      t' : {!!}
      t' = plift {!!}
      -- dp : {!!}
      -- dp = depth-preserving γ {!s!} {!!}
      t≤γ : t .proj₁ ≤ γ
      t≤γ = ≤≤ s≤γ (≡→≤ {!!})

  ϕ-inj≈ : ∀ {t̃ ũ} → (∀ x → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ])
         → Colim D^X [ t̃ ≈ ũ ]
  ϕ-inj≈ {α , t̂} {β , û} p =
       α , t̂
    ≈⟨ ≈lstep ∨ᶻ-l t̂ ⟩
       γ , (λ x → D.hom (box ∨ᶻ-l) (t̂ x))
    ≈⟨ ≈lstage (α ∨ᶻ β) (≡.funExt q) ⟩
       γ , (λ x → D.hom (box ∨ᶻ-r) (û x))
    ≈⟨ ≈lsym (≈lstep ∨ᶻ-r û) ⟩
      β , û ∎
    where
    open ≈.≈syntax {S = Colim D^X}
    γ : Z
    γ = α ∨ᶻ β
    q : ∀ x → D.hom (box ∨ᶻ-l) (t̂ x) ≡ D.hom (box ∨ᶻ-r) (û x)
    q x = join≈ (p (lower x)) ∨ᶻ-l ∨ᶻ-r

  --   let
  --     w : D̃ γ /≈
  --     w = D.hom (box ∨ᶻ-l) {!!} in {!!}
  
  -- ϕ-inj : ∀ {t̃ ũ} → (∀ x → ϕ t̃ x ≡ ϕ ũ x) → t̃ ≡ ũ
  -- ϕ-inj {t̃} {ũ} = {!!}

  -- ϕ-surj≈ : (f : X → Colim/≈ D) → ∃ λ t̃ → ϕ t̃ ≡ f
  -- ϕ-surj≈ f = ∣ {!!} , {!!} ∣

  -- ϕ-surj : (f : X → Colim/≈ D) → ∃ λ t̃ → ϕ t̃ ≡ f
  -- ϕ-surj f = {!!}

  -- lemma : Colim/≈ D^X ≅ (X → Colim/≈ D)
  -- lemma = Bijection→Iso ϕ ((λ p → ϕ-inj (≡.funExt⁻ p)) , ϕ-surj)
