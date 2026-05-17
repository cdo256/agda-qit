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
  plift≈ {α} = elim (D̃ α) Q f f-cong
    where
    module Dα = SetoidQuotient (D̃ α)
    Q : D̃ α /≈ → Set (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
    Q t̂ = D̃ (rankD t̂) /≈
    f : (t̂ : D₀ α) → Q Dα.[ t̂ ]
    f t̂ = D̃ (rankD₀ t̂) ⊢[ plift t̂ ]
    f-cong' : ∀ {ŝ t̂ : D₀ α} → (p : Dα.[ ŝ ] ≡ Dα.[ t̂ ])
           → subst Q p (f ŝ) ≡ f t̂
    f-cong' p = {!!}
    f-cong : ∀ {ŝ t̂ : D₀ α} → (p : D̃ α [ ŝ ≈ t̂ ])
           → subst Q Dα.≈[ p ] (f ŝ) ≡ f t̂
    f-cong (≈pcong a μ f₁ g r) = {!!}
    f-cong (≈psat e ϕ l≤α r≤α) = {!!}
    f-cong ≈prefl = ≡.refl
    f-cong (≈psym p) = ≡.dsym Q Dα.≈[ p ] (f-cong p)
    f-cong (≈ptrans p q) = ≡.dtrans Q Dα.≈[ p ] Dα.≈[ q ] (f-cong p) (f-cong q)
    f-cong (≈pweaken α≤β p) = {!!}

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
