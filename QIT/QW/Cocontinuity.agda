open import QIT.Prelude hiding (ℓD)
open import QIT.Prop
open import QIT.Setoid
open import QIT.Set.Base
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties renaming (_∘_ to _∘ꟳ_)
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Set.Bijection
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient
open import QIT.Plump.Algebra

module QIT.QW.Cocontinuity 
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  {ℓZ ℓ< ℓ≤ : Level}
  (Zᴬ : PlumpAlgebra (sig .Sig.S) (sig .Sig.P) ℓZ ℓ< ℓ≤)
  where

open Sig sig
open A!C a!c*
open FunExt funExt*

open import QIT.QW.StageColimit sig Zᴬ

import QIT.Plump.Properties

module _ where
  open import QIT.Container.Base
  open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
  open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))
  open import QIT.Setoid.Quotient

  open import QIT.QW.Algebra sig
  -- open import QIT.QW.Colimit ≤p ℓD ℓD' hiding (_≈ˡ_)

  private
    ℓc = ℓA ⊔ ℓS ⊔ ℓP
    ℓc' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV

  Cocontinuous : (F : Functor (SetCat (ℓc ⊔ ℓc')) (SetCat (ℓc ⊔ ℓc'))) (D : Diagram/≈ ℓc ℓc')
                → Prop ℓc'
  Cocontinuous F D =
    Colim/≈ (F ∘ꟳ D) ≅ Functor.ob F (Colim/≈ D)

  module ColimF∘D = SQ (Colim (F ∘ D))
  module ColimD = SQ (Colim D)
  module Ob = Functor F
  open SQ

  module _ (depth-preserving : ∀ (s t : T) → s ≈ᵗ t → ιᶻ s ≡ ιᶻ t) where
    module PreservationByPowers (s : S) where
      abstract 
        rankD₀ : ∀ {α} → D₀ α → Z
        rankD₀ (t , _) = ιᶻ t

        rankD-cong : ∀ {α} {ŝ t̂ : D₀ α} → ŝ ≈ˢ t̂ → rankD₀ ŝ ≡ rankD₀ t̂
        rankD-cong {α} {s , _} {t , _} p = depth-preserving s t p

        rankD : ∀ {α} → D̃ α /≈ → Z
        rankD {α} = rec (D̃ α) rankD₀ rankD-cong

        rankD-beta : ∀ {α} (t̂ : D₀ α) → rankD (D̃ α ⊢[ t̂ ]) ≡ rankD₀ t̂
        rankD-beta {α} t̂ = rec-beta (D̃ α) rankD₀ rankD-cong t̂

        hom-beta : ∀ {α β} (p : α ≤ β) (t̂ : D₀ α)
                → D/≈.hom (box p) (D̃ α ⊢[ t̂ ]) ≡ D̃ β ⊢[ dweaken₀ p t̂ ]
        hom-beta {α} {β} p t̂ =
          rec-beta (D̃ α)
            (λ x → D̃ β ⊢[ dweaken₀ p x ])
            (λ {x y} q → D̃ β ⊢≈[ q ])
            t̂

        rankD-step : ∀ {α β} (p : α ≤ β) (t̂ : D₀ α)
                      → rankD (D̃ α ⊢[ t̂ ]) ≡ rankD (D/≈.hom (box p) (D̃ α ⊢[ t̂ ]))
        rankD-step p t̂ =
          ≡.trans (rankD-beta t̂)
            (≡.trans (≡.sym (rankD-beta (dweaken₀ p t̂)))
              (≡.cong rankD (≡.sym (hom-beta p t̂))))

        rankC : Colim/≈ D → Z
        rankC = rec (Colim D) (λ (_ , t̂) → rankD t̂) stable
          where
          stable : ∀ {x y} → Colim D [ x ≈ y ] → rankD (x .proj₂) ≡ rankD (y .proj₂)
          stable (≈lstage i p) = ≡.cong rankD p
          stable (≈lstep {α} {β} p x) =
            elimp (D̃ α)
                  (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
                  (rankD-step p)
                  x
          stable (≈lsym p) = ≡.sym (stable p)
          stable (≈ltrans p q) = ≡.trans (stable p) (stable q)

        dlift₀ : ∀ {α} (t̂ : D₀ α) → D₀ (rankD₀ t̂)
        dlift₀ (t , _) = t , ≤refl (ιᶻ t)

        dlift : ∀ {α} → (t̂ : D₀ α) → D̃ (rankD₀ t̂) /≈
        dlift {α} t̂ = D̃ (rankD₀ t̂) ⊢[ dlift₀ t̂ ]

        -- open ≡.≡-Reasoning
        -- open import QIT.Setoid.Properties using (transport≈; castˡ; castʳ)

        dlift-dsup : ∀ a μ (f : ∀ i → D₀ (μ i))
          → dlift₀ (dsup₀ a μ f) ≡ {!dsup₀ a {!rankD₀ ∘ f!} {!λ i → plift₀ (f i)!}!}
        dlift-dsup a μ f = ≡.refl

    --     exactify : ∀ {γ} (ŝ t̂ : D₀ γ) (p : ŝ ≈ˢ t̂)
    --       → plift₀ ŝ ≈ˢ subst D₀ (≡.sym (rankD-cong p)) (plift₀ t̂)
    --     exactify {γ} (s , s≤γ) (t , t≤γ) p =
    --       ≈ttrans p q
    --       where
    --       dp : ιᶻ t ≡ ιᶻ s 
    --       dp = (≡.sym (rankD-cong p))
    --       q : t ≈ᵗ subst D₀ dp (t , ≤refl _) .fst
    --       q = ≡.substp (t ≈ᵗ_) (≡.cong fst r) ≈trefl
    --         where
    --         r : (t , ≡.substp (t ≤ᵀ_) dp (≤refl _))
    --           ≡ ≡.subst D₀ dp (t , ≤refl _)
    --         r = ≡.sym (≡.subst-ΣP (λ α t → t ≤ᵀ α) dp (t , ≤refl _))

      rankD-step : ∀ {α β} (p : α ≤ β) (t̂ : D₀ α)
                     → rankD (D̃ α ⊢[ t̂ ]) ≡ rankD (D/≈.hom (box p) (D̃ α ⊢[ t̂ ]))
      rankD-step p t̂ =
        ≡.trans (rankD-beta t̂)
          (≡.trans ≡.refl
            (≡.trans (≡.sym (rankD-beta (pweaken p t̂)))
              (≡.cong rankD (≡.sym (hom-beta p t̂)))))

      rankC : Colim/≈ D → Z
      rankC = rec (Colim D) (λ (_ , t̂) → rankD t̂) stable
        where
        stable : ∀ {x y} → Colim D [ x ≈ y ] → rankD (x .proj₂) ≡ rankD (y .proj₂)
        stable (≈lstage i p) = ≡.cong rankD p
        stable (≈lstep {α} {β} p x) =
          elimp (D̃ α)
                (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
                (rankD-step p)
                x
        stable (≈lsym p) = ≡.sym (stable p)
        stable (≈ltrans p q) = ≡.trans (stable p) (stable q)

      plift : ∀ {α} → (t̂ : D₀ α) → D₀ (rankD₀ t̂)
      plift (t , _) = t , ≤refl (ιᶻ t)

      plift₀ : ∀ {α} → (t̂ : D₀ α) → D̃ (rankD₀ t̂) /≈
      plift₀ {α} (t , t≤α) = D̃ (ιᶻ t) ⊢[ t , ≤refl _ ]

      same-stage : ∀ {α} {t : T} (p q : t ≤ᵀ α) → D̃ α [ (t , p) ≈ (t , q) ]
      same-stage p q = ≡→≈ (D̃ _) (ΣP≡ (_ , p) (_ , q) ≡.refl)

      module Plift≈Helper {α} where
        module Dα = SQ (D̃ α)
        open ≡.≡-Reasoning

        castʳ : ∀ {γ} {x y z : D₀ γ} → y ≡ z → D̃ γ [ x ≈ y ] → D̃ γ [ x ≈ z ]
        castʳ ≡.refl p = p

        castˡ : ∀ {γ} {x y z : D₀ γ} → x ≡ y → D̃ γ [ x ≈ z ] → D̃ γ [ y ≈ z ]
        castˡ ≡.refl p = p

        cast-rhs : ∀ {γ s t} {ps : s ≤ᵀ γ} {pt qt : t ≤ᵀ γ}
          → D̃ γ [ (s , ps) ≈ (t , pt) ]
          → D̃ γ [ (s , ps) ≈ (t , qt) ]
        cast-rhs {pt = pt} {qt = qt} p = ≈ptrans p (same-stage pt qt)

        transport≈ : ∀ {γ δ} (p : γ ≡ δ) {x y : D₀ γ}
          → D̃ γ [ x ≈ y ] → D̃ δ [ subst D₀ p x ≈ subst D₀ p y ]
        transport≈ {γ} ≡.refl {x} {y} r =
          ≡.substp₂ (D̃ γ [_≈_])
            (≡.sym (≡.subst-refl x))
            (≡.sym (≡.subst-refl y))
            r

        subst-D₀-fst : ∀ {γ δ : Z} (p : γ ≡ δ) (û : D₀ γ)
                     → subst D₀ p û .fst ≡ û .fst
        subst-D₀-fst {γ} ≡.refl û =
          ≡.cong {A = D₀ γ} {B = T} fst
                 {≡.subst D₀ ≡.refl û} {û}
                 (≡.subst-refl û)

        plift-fst : ∀ {γ} (û : D₀ γ) → (plift û) .fst ≡ û .fst
        plift-fst û = ≡.refl

        plift-psup : ∀ a μ (f : ∀ i → D₀ (μ i))
          → plift (psup a μ f)
          ≡ psup a (λ i → rankD₀ (f i)) (λ i → plift (f i))
        plift-psup a μ f = ΣP≡ _ _ ≡.refl

        exactify : ∀ {γ} {ŝ t̂ : D₀ γ} (p : D̃ γ [ ŝ ≈ t̂ ])
          → D̃ (rankD₀ ŝ) [ plift ŝ
                         ≈ subst D₀ (≡.sym (rankD-cong p)) (plift t̂) ]
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
            rhsfst = ≡.trans (≡.cong (λ h → W.sup (a , h)) (funExt g'fst))
                              (≡.sym (subst-D₀-fst (≡.sym dp) (plift (psup a μ g))))
        exactify (≈psat e ϕ l≤α r≤α) = castʳ rhs≈ base
          where
          dp : rankD₀ (lhs' e ϕ , l≤α) ≡ rankD₀ (rhs' e ϕ , r≤α)
          dp = rankD-cong (≈psat e ϕ l≤α r≤α)
          base : D̃ (rankD₀ (lhs' e ϕ , l≤α)) [ plift (lhs' e ϕ , l≤α) ≈ (rhs' e ϕ , ≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _)) ]
          base = ≈psat e ϕ (≤refl _) (≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _))
          rhs≈ : (rhs' e ϕ , ≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _)) ≡ subst D₀ (≡.sym dp) (plift (rhs' e ϕ , r≤α))
          rhs≈ = ΣP≡ _ _ (≡.sym (subst-D₀-fst (≡.sym dp) (plift (rhs' e ϕ , r≤α))))
        exactify {ŝ = ŝ} {t̂ = t̂} ≈prefl =
          ≡→≈ (D̃ (rankD₀ ŝ)) (≡.sym (≡.subst-refl (plift ŝ)))
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
          rhs≈ = ≡.subst-subst D₀ (≡.sym dq) (≡.sym dp) (plift û)
        exactify (≈pweaken α≤β p) = exactify p

        shiftRepresentative : ∀ {γ δ} {û : D₀ δ} (p : γ ≡ δ)
          → subst (λ β → D̃ β /≈) p (D̃ γ ⊢[ subst D₀ (≡.sym p) û ])
          ≡ D̃ δ ⊢[ û ]
        shiftRepresentative {γ} {δ} {û} ≡.refl =
          ≡.trans (≡.subst-refl _) (≡.cong (D̃ γ ⊢[_]) (≡.subst-refl û))

        plift₀-cong : ∀ {γ} {ŝ t̂ : D₀ γ} (p : D̃ γ [ ŝ ≈ t̂ ])
          → subst D̃/≈ (rankD-cong p) (plift₀ ŝ) ≡ plift₀ t̂
        plift₀-cong {ŝ = ŝ} {t̂ = t̂} p =
          ≡.trans
            (≡.cong (subst D̃/≈ (rankD-cong p)) (D̃ (rankD₀ ŝ) ⊢≈[ exactify p ]))
            (shiftRepresentative (rankD-cong p))

      plift≈ : ∀ {α} → (t̂ : D̃ α /≈) → D̃ (rankD t̂) /≈
      plift≈ {α} = elim (D̃ α) (λ t̂ → D̃ (rankD t̂) /≈) u p
        where
        module H = Plift≈Helper {α}
        open ≡.≡-Reasoning

        u : (t̂ : S.D₀ α) → D̃ (rankD (D̃ α ⊢[ t̂ ])) /≈
        u t̂ = subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong t̂)) (plift₀ t̂)

        p : ∀ {ŝ t̂} (q : D̃ α [ ŝ ≈ t̂ ])
          → subst (λ t̂ → D̃ (rankD t̂) /≈) (D̃ α ⊢≈[ q ]) (u ŝ) ≡ u t̂
        p {ŝ} {t̂} q =
          subst (λ t̃ → D̃ (rankD t̃) /≈) (D̃ α ⊢≈[ q ])
                (subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong ŝ)) (plift₀ ŝ))
            ≡⟨ ≡.subst-cong D̃/≈ rankD (D̃ α ⊢≈[ q ]) (subst D̃/≈ _ (plift₀ ŝ)) ⟩
          subst D̃/≈ (≡.cong rankD (D̃ α ⊢≈[ q ]))
                (subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong ŝ)) (plift₀ ŝ))
            ≡⟨ ≡.subst-subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong ŝ))
                             (≡.cong rankD (D̃ α ⊢≈[ q ])) (plift₀ ŝ) ⟩
          subst D̃/≈ (≡.trans (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong ŝ))
                             (≡.cong rankD (D̃ α ⊢≈[ q ])))
                    (plift₀ ŝ)
            ≡⟨ ≡.trans
                 (≡.congp (λ r → subst D̃/≈ r (plift₀ ŝ)))
                 (≡.sym (≡.subst-subst D̃/≈ (rankD-cong q)
                                         (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong t̂))
                                         (plift₀ ŝ))) ⟩
          subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong t̂))
                (subst D̃/≈ (rankD-cong q) (plift₀ ŝ))
            ≡⟨ ≡.cong (subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong t̂))) (H.plift₀-cong q) ⟩
          subst D̃/≈ (≡.sym (rec-beta (D̃ α) rankD₀ rankD-cong t̂)) (plift₀ t̂) ∎

    --     f : D₀ α → Σ Z (λ β → D̃ β /≈)
    --     f t̂ = rankD₀ t̂ , D̃ (rankD₀ t̂) ⊢[ plift t̂ ]

    --     u : ∀ {γ δ} {û : D₀ δ} (p : γ ≡ δ)
    --       → subst (λ β → D̃ β /≈) p (D̃ γ ⊢[ subst D₀ (≡.sym p) û ])
    --       ≡ D̃ δ ⊢[ û ]
    --     shiftRep ≡.refl = ≡.refl

    --     plift-cong : ∀ {γ} {ŝ t̂ : D₀ γ} (p : D̃ γ [ ŝ ≈ t̂ ])
    --       → subst D̃/≈ (rankD-cong p) (plift ŝ) ≡ plift t̂
    --     plift-cong {γ} {ŝ = ŝ} {t̂ = t̂} p =
    --       ≡.trans
    --         (≡.cong (subst D̃/≈ (rankD-cong p)) (D̃ (rankD₀ ŝ) ⊢≈[ exactify ŝ t̂ p ]))
    --         (shiftRep (rankD-cong p))

    --     d : D̃ α /≈ → Σ Z (λ β → D̃ β /≈)
    --     d = rec (D̃ α) f f-cong

    --     first : ∀ t̂ → (d t̂) .proj₁ ≡ rankD t̂
    --     first = elimp (D̃ α) (λ t̂ → (d t̂) .proj₁ ≡ rankD t̂)
    --       (λ û → ≡.trans (≡.cong proj₁ (rec-beta (D̃ α) f f-cong û)) (≡.sym (rankD-beta û)))

    --     plift≈ : (t̂ : D̃ α /≈) → D̃ (rankD t̂) /≈
    --     plift≈ t̂ = subst (λ β → D̃ β /≈) (first t̂) ((d t̂) .proj₂)


    --   s≤rankD : ∀ {α} (t̂ : D₀ α) → t̂ .fst ≤ᵀ rankD (D̃ α ⊢[ t̂ ])
    --   s≤rankD {α} t̂ = ≡.substp (t̂ .fst ≤ᵀ_) (≡.sym (rankD-beta t̂)) (≤refl (rankD₀ t̂))

    --   _~ᵀ_ : ∀ (s t : T) → Prop _
    --   s ~ᵀ t = ιᶻ s ≡ ιᶻ t

    --   _~⁰_ : ∀ {α β} → D₀ α → D₀ β → Prop _
    --   (s , _) ~⁰ (t , _) = s ~ᵀ t

    --   _~∀_ : ∀ {α β} → D̃ α /≈ → D̃ β /≈ → Prop _
    --   _~∀_ = QuotHetRel∀ D̃ _~⁰_

    --   _~∃_ : ∀ {α β} → D̃ α /≈ → D̃ β /≈ → Prop _
    --   _~∃_ = QuotHetRel∃ D̃ _~⁰_

    --   ~∀→∃ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → ŝ ~∀ t̂ → ŝ ~∃ t̂
    --   ~∀→∃ = QuotHetRel∀→∃ D̃ _~⁰_

    --   ~∃→∀ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → ŝ ~∃ t̂ → ŝ ~∀ t̂
    --   ~∃→∀ {α} {β} ŝ t̂ ∣ qrwitness (s' , s'≤α) (t' , t'≤β) r ps' pt' ∣ (s , s≤α) (t , t≤β) ps pt = p
    --     where
    --     module Dα = SQ (D̃ α)
    --     module Dβ = SQ (D̃ β)

    --     rs : D̃ α [ (s , s≤α) ≈ (s' , s'≤α) ]
    --     rs = Dα.effectiveness _ _ (≡.trans ps (≡.sym ps'))

    --     rt : D̃ β [ (t' , t'≤β) ≈ (t , t≤β) ]
    --     rt = Dβ.effectiveness _ _ (≡.trans pt' (≡.sym pt))

    --     qs : s ~ᵀ s'
    --     qs = depth-preserving α (s , s≤α) (s' , s'≤α) rs

    --     qt : t' ~ᵀ t
    --     qt = depth-preserving β (t' , t'≤β) (t , t≤β) rt

    --     p : (s , s≤α) ~⁰ (t , t≤β)
    --     p = ≡.trans qs (≡.trans r qt)

    --   ~⇔ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → (ŝ ~∀ t̂) ⇔ (ŝ ~∃ t̂)
    --   ~⇔ ŝ t̂ = ~∀→∃ ŝ t̂ , ~∃→∀ ŝ t̂

    --   _~ᶜ⁰_ : Colim₀ D → Colim₀ D → Prop _
    --   (α , ŝ) ~ᶜ⁰ (β , t̂) = ŝ ~∀ t̂

    --   _~ᶜ∃⁰_ : Colim₀ D → Colim₀ D → Prop _
    --   (α , ŝ) ~ᶜ∃⁰ (β , t̂) = ŝ ~∃ t̂

    --   _~ᶜ∀_ : Colim/≈ D → Colim/≈ D → Prop _
    --   _~ᶜ∀_ = QuotHomRel∀ (Colim D) _~ᶜ⁰_

    --   _~ᶜ∃_ : Colim/≈ D → Colim/≈ D → Prop _
    --   _~ᶜ∃_ = QuotHomRel∃ (Colim D) _~ᶜ⁰_

    --   ~ᶜ∀→∃ : ∀ (x y : Colim/≈ D) → x ~ᶜ∀ y → x ~ᶜ∃ y
    --   ~ᶜ∀→∃ = QuotHomRel∀→∃ (Colim D) _~ᶜ⁰_

    --   ~ᶜ∃→∀ : ∀ (x y : Colim/≈ D) → x ~ᶜ∃ y → x ~ᶜ∀ y
    --   ~ᶜ∃→∀ x y ∣ qrwitness (α , x₀) (β , y₀) r px py ∣
    --     (α' , ŝ) (β' , t̂) ≡.refl ≡.refl
    --     (s , s≤) (t , t≤) ≡.refl ≡.refl =
    --       ≡.trans (rep-rank (s , s≤) ≡.refl)
    --         (≡.trans mid (≡.sym (rep-rank (t , t≤) ≡.refl)))
    --     where
    --     open Setoid (Colim D)
    --     open ≈.≈syntax {S = Colim D}

    --     rank~ : ∀ {γ δ} {û : D̃ γ /≈} {v̂ : D̃ δ /≈} → û ~∀ v̂ → rankD û ≡ rankD v̂
    --     rank~ {γ} {δ} {û} {v̂} u~v = Dγ.elimp Pred f û v̂ u~v
    --       where
    --       module Dγ = SQ (D̃ γ)
    --       module Dδ = SQ (D̃ δ)

    --       Pred : D̃ γ /≈ → Prop _
    --       Pred û = ∀ v̂ → û ~∀ v̂ → rankD û ≡ rankD v̂

    --       f : ∀ u₀ → Pred (D̃ γ ⊢[ u₀ ])
    --       f u₀ v̂ = Dδ.elimp Pred' g v̂
    --         where
    --         Pred' : D̃ δ /≈ → Prop _
    --         Pred' v̂ = (D̃ γ ⊢[ u₀ ]) ~∀ v̂ → rankD (D̃ γ ⊢[ u₀ ]) ≡ rankD v̂

    --         g : ∀ v₀ → Pred' (D̃ δ ⊢[ v₀ ])
    --         g v₀ p = ≡.trans (rankD-beta u₀)
    --                 (≡.trans (p u₀ v₀ ≡.refl ≡.refl)
    --                           (≡.sym (rankD-beta v₀)))

    --     rep-rank : ∀ {γ} (u₀ : D₀ γ) {û : D̃ γ /≈}
    --       → D̃ γ ⊢[ u₀ ] ≡ û → rankD₀ u₀ ≡ rankD û
    --     rep-rank u₀ pu = ≡.trans (≡.sym (rankD-beta u₀)) (≡.cong rankD pu)

    --     rank≈ : ∀ {γ δ} {û : D̃ γ /≈} {v̂ : D̃ δ /≈}
    --       → Colim D [ γ , û ≈ δ , v̂ ] → rankD û ≡ rankD v̂
    --     rank≈ (≈lstage i e) = ≡.cong rankD e
    --     rank≈ (≈lstep {i = γ} p û) =
    --       elimp (D̃ γ)
    --             (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
    --             (rankD-step p)
    --             û
    --     rank≈ (≈lsym p) = ≡.sym (rank≈ p)
    --     rank≈ (≈ltrans p q) = ≡.trans (rank≈ p) (rank≈ q)

    --     ŝ≈x₀ : Colim D [ α' , ŝ ≈ α , x₀ ]
    --     ŝ≈x₀ = begin
    --       α' , ŝ
    --         ≈⟨ ColimD.effectiveness (α' , ŝ) (α , x₀) (≡.sym px) ⟩
    --       α , x₀ ∎

    --     y₀≈t̂ : Colim D [ β , y₀ ≈ β' , t̂ ]
    --     y₀≈t̂ = begin
    --       β , y₀
    --         ≈⟨ ColimD.effectiveness (β , y₀) (β' , t̂) py ⟩
    --       β' , t̂ ∎

    --     mid : rankD ŝ ≡ rankD t̂
    --     mid = ≡.trans (rank≈ ŝ≈x₀) (≡.trans (rank~ r) (rank≈ y₀≈t̂))

    --   ~ᶜ⇔ : ∀ (x y : Colim/≈ D) → (x ~ᶜ∀ y) ⇔ (x ~ᶜ∃ y)
    --   ~ᶜ⇔ x y = ~ᶜ∀→∃ x y , ~ᶜ∃→∀ x y

    --   X = P s
    --   D^X : Diagram/≈ ℓc ℓc'
    --   D^X = _^_ {ℓc} {ℓc'} D (Lift (ℓA ⊔ ℓS) X)
    --   module D^X = Functor D^X
    --   module ColimD^X = SQ (Colim D^X)

    --   ϕ₀ : Colim₀ D^X → X → Colim₀ D
    --   ϕ₀ (α , t̂) x = α , t̂ (lift x)

    --   ϕ-cong : ∀ {t̃ ũ} → Colim D^X [ t̃ ≈ ũ ] → (x : X) → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ]
    --   ϕ-cong {α , t̂} {α , t̂} (≈lstage α ≡.refl) x = ≡→≈ (Colim D) ≡.refl
    --   ϕ-cong {α , t̂} {β , û} (≈lstep p t̂) x = ≈lstep p (t̂ (lift x))
    --   ϕ-cong {α , t̂} {β , û} (≈lsym p) x = ≈lsym (ϕ-cong p x)
    --   ϕ-cong {α , t̂} {β , û} (≈ltrans p q) x = ≈ltrans (ϕ-cong p x) (ϕ-cong q x)

    --   ϕ : Colim/≈ D^X → (X → Colim/≈ D)
    --   ϕ f̃ x = ColimD^X.map (Colim D) (λ f → ϕ₀ f x) (λ p → ϕ-cong p x) f̃

    --   module _ {α β : Z} (α≤β : α ≤ β) where
    --     module Bα = Bounded D α
    --     module Bβ = Bounded D β

    --     map≤₀ : Bα.Colim≤₀ → Bβ.Colim≤₀
    --     map≤₀ (i≤α , x) = (i≤α .fst , ≤≤ α≤β (i≤α .snd)) , x

    --     map≈≤ : ∀ {s t} → Bα._≈ˡ≤_ s t → Bβ._≈ˡ≤_ (map≤₀ s) (map≤₀ t)
    --     map≈≤ (Bα.≈l≤stage ι e) = Bβ.≈l≤stage (ι .fst , ≤≤ α≤β (ι .snd)) e
    --     map≈≤ (Bα.≈l≤step p x) = Bβ.≈l≤step p x
    --     map≈≤ (Bα.≈l≤sym r) = Bβ.≈l≤sym (map≈≤ r)
    --     map≈≤ (Bα.≈l≤trans r₁ r₂) = Bβ.≈l≤trans (map≈≤ r₁) (map≈≤ r₂)

    --   module _ where
    --     open Bounded D renaming (_≈ˡ≤_ to _⊢_≈ˡ≤_)
    --     sameBounded : ∀ {γ α} (p q : α ≤ γ) {y : D̃ α /≈}
    --       → γ ⊢ ((α , p) , y) ≈ˡ≤ ((α , q) , y)
    --     sameBounded {γ} {α} p q {y} = B.≈l≤trans (B.≈l≤step (≤refl α) y) (B.≈l≤stage (α , q) eq)
    --       where
    --       module B = Bounded D γ
    --       module Dα = SQ (D̃ α)
    --       module D∣γ = Functor (RestrictDiagram D γ)
    --       hom-refl : (y : D̃ α /≈) → D∣γ.hom {α , p} {α , p} (box (≤refl α)) y ≡ y
    --       hom-refl = Dα.elimp (λ y → D∣γ.hom {α , p} {α , p} (box (≤refl α)) y ≡ y) h
    --         where
    --         h : ∀ t̂ → D/≈.hom (box (≤refl α)) (D̃ α ⊢[ t̂ ]) ≡ D̃ α ⊢[ t̂ ]
    --         h t̂ rewrite rec-beta (D̃ α) (λ x → D̃ α ⊢[ pweaken (≤refl α) x ]) (λ {x y} p → D̃ α ⊢≈[ p ]) t̂ =
    --           D̃ α ⊢≈[ same-stage _ _ ]
    --       eq : D∣γ.hom {α , p} {α , p} (box (≤refl α)) y ≡ y
    --       eq = hom-refl y

    --     record BoundedJoin (x y : Colim₀ D) : Set (ℓA ⊔ ℓS ⊔ ℓP ⊔ lsuc ℓV ⊔ ℓE) where
    --       constructor bjoin
    --       private
    --         α = x .proj₁
    --         β = y .proj₁
    --         s̃ = x .proj₂
    --         t̃ = y .proj₂
    --       field
    --         γ : Z
    --         α≤γ : α ≤ γ
    --         β≤γ : β ≤ γ
    --         γ⊢x≈y : γ ⊢ ((α , α≤γ) , s̃) ≈ˡ≤ ((β , β≤γ) , t̃)

    --     boundedJoin : ∀ {α β} {x : D̃ α /≈} {y : D̃ β /≈}
    --       → Colim D [ α , x ≈ β , y ]
    --       → ∥ BoundedJoin (α , x) (β , y) ∥
    --     boundedJoin = recˡ D C sC pC syC trC
    --       where
    --       C : ∀ {s t} → Colim D [ s ≈ t ] → Prop _
    --       C {α , x} {β , y} _ = ∥ BoundedJoin (α , x) (β , y) ∥

    --       sC : ∀ α {x x'} (e : x ≡ x') → C (≈lstage α e)
    --       sC α e = ∣ bjoin α (≤refl α) (≤refl α) (≈l≤stage (α , ≤refl α) e) ∣

    --       pC : ∀ {α β} (p : α ≤ β) (x : D̃ α /≈) → C (≈lstep p x)
    --       pC {α} {β} p x = ∣ bjoin β p (≤refl β) (≈l≤step p x) ∣

    --       syC : ∀ {s t} (r : Colim D [ s ≈ t ]) → C r → C (≈lsym r)
    --       syC {α , x} {β , y} r ∣ bjoin γ α≤γ β≤γ γ⊢x≈y ∣ = ∣ bjoin γ β≤γ α≤γ (≈l≤sym γ⊢x≈y) ∣

    --       trC : ∀ {s t u} (r₁ : Colim D [ s ≈ t ]) (r₂ : Colim D [ t ≈ u ]) → C r₁ → C r₂ → C (≈ltrans r₁ r₂)
    --       trC {α , x} {β , y} {δ , z} r₁ r₂
    --           ∣ bjoin γ₁ α≤γ₁ β≤γ₁ γ₁⊢x≈y ∣
    --           ∣ bjoin γ₂ β≤γ₂ δ≤γ₂ γ₂⊢y≈z ∣ =
    --         ∣ bjoin γ α≤γ δ≤γ (≈l≤trans γ⊢x≈y (≈l≤trans γ⊢y≈y γ⊢y≈z)) ∣
    --         where
    --         γ : Z
    --         γ = γ₁ ∨ᶻ γ₂

    --         α≤γ : α ≤ γ
    --         α≤γ = ≤≤ ∨ᶻ-l α≤γ₁

    --         δ≤γ : δ ≤ γ
    --         δ≤γ = ≤≤ ∨ᶻ-r δ≤γ₂

    --         β≤γˡ : β ≤ γ
    --         β≤γˡ = ≤≤ ∨ᶻ-l β≤γ₁

    --         β≤γʳ : β ≤ γ
    --         β≤γʳ = ≤≤ ∨ᶻ-r β≤γ₂

    --         γ⊢x≈y : γ ⊢ ((α , α≤γ) , x) ≈ˡ≤ ((β , β≤γˡ) , y)
    --         γ⊢x≈y = map≈≤ ∨ᶻ-l γ₁⊢x≈y

    --         γ⊢y≈z : γ ⊢ ((β , β≤γʳ) , y) ≈ˡ≤ ((δ , δ≤γ) , z)
    --         γ⊢y≈z = map≈≤ ∨ᶻ-r γ₂⊢y≈z

    --         γ⊢y≈y : γ ⊢ ((β , β≤γˡ) , y) ≈ˡ≤ ((β , β≤γʳ) , y)
    --         γ⊢y≈y = sameBounded β≤γˡ β≤γʳ

    --     rankColim : ∀ {γ δ} {x : D̃ γ /≈} {y : D̃ δ /≈}
    --               → Colim D [ γ , x ≈ δ , y ] → rankD x ≡ rankD y
    --     rankColim (≈lstage i e) = ≡.cong rankD e
    --     rankColim (≈lstep {i = γ} p x) =
    --       elimp (D̃ γ)
    --             (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
    --             (rankD-step p)
    --             x
    --     rankColim (≈lsym p) = ≡.sym (rankColim p)
    --     rankColim (≈ltrans p q) = ≡.trans (rankColim p) (rankColim q)

    --     sameHom : ∀ {α γ} (p q : α ≤ γ) {x : D̃ α /≈}
    --             → D.hom (box p) x ≡ D.hom (box q) x
    --     sameHom {α} {γ} p q {x} = Dα.elimp B h x
    --       where
    --       module Dα = SQ (D̃ α)
    --       B : D̃ α /≈ → Prop _
    --       B x = D.hom (box p) x ≡ D.hom (box q) x
    --       h : ∀ û → B (D̃ α ⊢[ û ])
    --       h û@(t , t≤α) =
    --         ≡.trans (hom-beta p û)
    --           (≡.trans (D̃ γ ⊢≈[ same-stage (≤≤ p t≤α) (≤≤ q t≤α) ])
    --             (≡.sym (hom-beta q û)))

    --     rankD≤stage : ∀ {α} (x : D̃ α /≈) → rankD x ≤ α
    --     rankD≤stage {α} = elimp (D̃ α) (λ x → rankD x ≤ α)
    --       (λ û@(t , t≤α) → ≡.substp (_≤ α) (≡.sym (rankD-beta û)) t≤α)

    --     toRankHom : ∀ {α} (x : D̃ α /≈) → ∀ {γ} (α≤γ : α ≤ γ)
    --               → D.hom (box α≤γ) x
    --               ≡ D.hom (box (≤≤ α≤γ (rankD≤stage x))) (plift≈ x)
    --     toRankHom {α} x {γ} α≤γ = elimp (D̃ α) Q u x 
    --       where
    --       open ≡.≡-Reasoning

    --       u : (t̂ : S.D₀ α) → D̃ (rankD (D̃ α ⊢[ t̂ ])) /≈
    --       u t̂ = subst D̃/≈ (≡.sym (rankD-beta t̂)) (plift t̂)

    --       p : ∀ {ŝ t̂} (q : D̃ α [ ŝ ≈ t̂ ])
    --         → subst (λ t̂ → D̃ (rankD t̂) /≈) (D̃ α ⊢≈[ q ]) (u ŝ) ≡ u t̂
    --       p {ŝ} {t̂} q =
    --         subst (λ t̃ → D̃ (rankD t̃) /≈) (D̃ α ⊢≈[ q ])
    --               (subst D̃/≈ (≡.sym (rankD-beta ŝ)) (plift ŝ))
    --           ≡⟨ ≡.subst-cong D̃/≈ rankD (D̃ α ⊢≈[ q ]) (subst D̃/≈ _ (plift ŝ)) ⟩
    --         subst D̃/≈ (≡.cong rankD (D̃ α ⊢≈[ q ]))
    --               (subst D̃/≈ (≡.sym (rankD-beta ŝ)) (plift ŝ))
    --           ≡⟨ ≡.subst-subst D̃/≈ (≡.sym (rankD-beta ŝ))
    --                           (≡.cong rankD (D̃ α ⊢≈[ q ])) (plift ŝ) ⟩
    --         subst D̃/≈ (≡.trans (≡.sym (rankD-beta ŝ))
    --                           (≡.cong rankD (D̃ α ⊢≈[ q ])))
    --                   (plift ŝ)
    --           ≡⟨ ≡.congp (λ r → subst D̃/≈ r (plift ŝ)) ⟩
    --         subst D̃/≈ {!!} (plift ŝ)
    --           ≡⟨ ≡.sym (≡.subst-subst D̃/≈ (rankD-cong q)
    --                                       (≡.sym (rankD-beta t̂))
    --                                       (plift ŝ)) ⟩
    --         subst D̃/≈ (≡.sym (rankD-beta t̂))
    --               (subst D̃/≈ (rankD-cong q) (plift ŝ))
    --           ≡⟨ ≡.cong (subst D̃/≈ (≡.sym (rankD-beta t̂)))
    --                     (plift-cong {α} {ŝ} {t̂} q) ⟩
    --         subst D̃/≈ (≡.sym (rankD-beta t̂)) (plift t̂) ∎

    -- --   s≤rankD : ∀ {α} (t̂ : D₀ α) → t̂ .fst ≤ᵀ rankD (D̃ α ⊢[ t̂ ])
    -- --   s≤rankD {α} t̂ = ≡.substp (t̂ .fst ≤ᵀ_) (≡.sym (rankD-beta t̂)) (≤refl (rankD₀ t̂))

    -- --   _~ᵀ_ : ∀ (s t : T) → Prop _
    -- --   s ~ᵀ t = ιᶻ s ≡ ιᶻ t

    -- --   _~⁰_ : ∀ {α β} → D₀ α → D₀ β → Prop _
    -- --   (s , _) ~⁰ (t , _) = s ~ᵀ t

    -- --   _~∀_ : ∀ {α β} → D̃ α /≈ → D̃ β /≈ → Prop _
    -- --   _~∀_ = QuotHetRel∀ D̃ _~⁰_

    -- --   _~∃_ : ∀ {α β} → D̃ α /≈ → D̃ β /≈ → Prop _
    -- --   _~∃_ = QuotHetRel∃ D̃ _~⁰_

    -- --   ~∀→∃ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → ŝ ~∀ t̂ → ŝ ~∃ t̂
    -- --   ~∀→∃ = QuotHetRel∀→∃ D̃ _~⁰_

    -- --   ~∃→∀ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → ŝ ~∃ t̂ → ŝ ~∀ t̂
    -- --   ~∃→∀ {α} {β} ŝ t̂ ∣ qrwitness (s' , s'≤α) (t' , t'≤β) r ps' pt' ∣ (s , s≤α) (t , t≤β) ps pt = p
    -- --     where
    -- --     module Dα = SetoidQuotient (D̃ α)
    -- --     module Dβ = SetoidQuotient (D̃ β)

    -- --     rs : D̃ α [ (s , s≤α) ≈ (s' , s'≤α) ]
    -- --     rs = Dα.effectiveness _ _ (≡.trans ps (≡.sym ps'))

    -- --     rt : D̃ β [ (t' , t'≤β) ≈ (t , t≤β) ]
    -- --     rt = Dβ.effectiveness _ _ (≡.trans pt' (≡.sym pt))

    -- --     qs : s ~ᵀ s'
    -- --     qs = depth-preserving s s' rs

    -- --     qt : t' ~ᵀ t
    -- --     qt = depth-preserving t' t rt

    -- --     p : (s , s≤α) ~⁰ (t , t≤β)
    -- --     p = ≡.trans qs (≡.trans r qt)

    -- --   ~⇔ : ∀ {α β} (ŝ : D̃ α /≈) (t̂ : D̃ β /≈) → (ŝ ~∀ t̂) ⇔ (ŝ ~∃ t̂)
    -- --   ~⇔ ŝ t̂ = ~∀→∃ ŝ t̂ , ~∃→∀ ŝ t̂

    -- --   _~ᶜ⁰_ : Colim₀ D → Colim₀ D → Prop _
    -- --   (α , ŝ) ~ᶜ⁰ (β , t̂) = ŝ ~∀ t̂

    -- --   _~ᶜ∃⁰_ : Colim₀ D → Colim₀ D → Prop _
    -- --   (α , ŝ) ~ᶜ∃⁰ (β , t̂) = ŝ ~∃ t̂

    -- --   _~ᶜ∀_ : Colim/≈ D → Colim/≈ D → Prop _
    -- --   _~ᶜ∀_ = QuotHomRel∀ (Colim D) _~ᶜ⁰_

    -- --   _~ᶜ∃_ : Colim/≈ D → Colim/≈ D → Prop _
    -- --   _~ᶜ∃_ = QuotHomRel∃ (Colim D) _~ᶜ⁰_

    -- --   ~ᶜ∀→∃ : ∀ (x y : Colim/≈ D) → x ~ᶜ∀ y → x ~ᶜ∃ y
    -- --   ~ᶜ∀→∃ = QuotHomRel∀→∃ (Colim D) _~ᶜ⁰_

    -- -- --   ~ᶜ∃→∀ : ∀ (x y : Colim/≈ D) → x ~ᶜ∃ y → x ~ᶜ∀ y
    -- -- --   ~ᶜ∃→∀ x y ∣ qrwitness (α , x₀) (β , y₀) r px py ∣
    -- -- --     (α' , ŝ) (β' , t̂) ≡.refl ≡.refl
    -- -- --     (s , s≤) (t , t≤) ≡.refl ≡.refl =
    -- -- --       ≡.trans (rep-rank (s , s≤) ≡.refl)
    -- -- --         (≡.trans mid (≡.sym (rep-rank (t , t≤) ≡.refl)))
    -- -- --     where
    -- -- --     open Setoid (Colim D)
    -- -- --     open ≈.≈syntax {S = Colim D}

    -- -- --     rank~ : ∀ {γ δ} {û : D̃ γ /≈} {v̂ : D̃ δ /≈} → û ~∀ v̂ → rankD û ≡ rankD v̂
    -- -- --     rank~ {γ} {δ} {û} {v̂} u~v = Dγ.elimp Pred f û v̂ u~v
    -- -- --       where
    -- -- --       module Dγ = SetoidQuotient (D̃ γ)
    -- -- --       module Dδ = SetoidQuotient (D̃ δ)

    -- -- --       Pred : D̃ γ /≈ → Prop _
    -- -- --       Pred û = ∀ v̂ → û ~∀ v̂ → rankD û ≡ rankD v̂

    -- -- --       f : ∀ u₀ → Pred (D̃ γ ⊢[ u₀ ])
    -- -- --       f u₀ v̂ = Dδ.elimp Pred' g v̂
    -- -- --         where
    -- -- --         Pred' : D̃ δ /≈ → Prop _
    -- -- --         Pred' v̂ = (D̃ γ ⊢[ u₀ ]) ~∀ v̂ → rankD (D̃ γ ⊢[ u₀ ]) ≡ rankD v̂

    -- -- --         g : ∀ v₀ → Pred' (D̃ δ ⊢[ v₀ ])
    -- -- --         g v₀ p = ≡.trans (rankD-beta u₀)
    -- -- --                 (≡.trans (p u₀ v₀ ≡.refl ≡.refl)
    -- -- --                           (≡.sym (rankD-beta v₀)))

    -- -- ϕinS : ∀ s (q : Colim/≈ (Pow.D^X s)) → ϕ (inS s q) ≡ (s , Pow.ϕ s q)
    -- -- ϕinS s = ColimPow.elimp B h
    -- --   where
    -- --   module Ps = Pow s
    -- --   module ColimPow = SQ (Colim (Ps.D^X))

    -- -- --     rank≈ : ∀ {γ δ} {û : D̃ γ /≈} {v̂ : D̃ δ /≈}
    -- -- --       → Colim D [ γ , û ≈ δ , v̂ ] → rankD û ≡ rankD v̂
    -- -- --     rank≈ (≈lstage i e) = ≡.cong rankD e
    -- -- --     rank≈ (≈lstep {i = γ} p û) =
    -- -- --       elimp (D̃ γ)
    -- -- --             (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
    -- -- --             (rankD-step p)
    -- -- --             û
    -- -- --     rank≈ (≈lsym p) = ≡.sym (rank≈ p)
    -- -- --     rank≈ (≈ltrans p q) = ≡.trans (rank≈ p) (rank≈ q)

    -- -- --     ŝ≈x₀ : Colim D [ α' , ŝ ≈ α , x₀ ]
    -- -- --     ŝ≈x₀ = begin
    -- -- --       α' , ŝ
    -- -- --         ≈⟨ ColimD.effectiveness (α' , ŝ) (α , x₀) (≡.sym px) ⟩
    -- -- --       α , x₀ ∎

    -- -- --     y₀≈t̂ : Colim D [ β , y₀ ≈ β' , t̂ ]
    -- -- --     y₀≈t̂ = begin
    -- -- --       β , y₀
    -- -- --         ≈⟨ ColimD.effectiveness (β , y₀) (β' , t̂) py ⟩
    -- -- --       β' , t̂ ∎

    -- -- --     mid : rankD ŝ ≡ rankD t̂
    -- -- --     mid = ≡.trans (rank≈ ŝ≈x₀) (≡.trans (rank~ r) (rank≈ y₀≈t̂))

    -- -- --   ~ᶜ⇔ : ∀ (x y : Colim/≈ D) → (x ~ᶜ∀ y) ⇔ (x ~ᶜ∃ y)
    -- -- --   ~ᶜ⇔ x y = ~ᶜ∀→∃ x y , ~ᶜ∃→∀ x y

    -- -- --   X = P s
    -- -- --   D^X : Diagram/≈ ℓc ℓc'
    -- -- --   D^X = _^_ {ℓc} {ℓc'} D (Lift (ℓA ⊔ ℓS) X)
    -- -- --   module D^X = Functor D^X
    -- -- --   module ColimD^X = SetoidQuotient (Colim D^X)

    -- -- --   ϕ₀ : Colim₀ D^X → X → Colim₀ D
    -- -- --   ϕ₀ (α , t̂) x = α , t̂ (lift x)

    -- -- --   ϕ-cong : ∀ {t̃ ũ} → Colim D^X [ t̃ ≈ ũ ] → (x : X) → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ]
    -- -- --   ϕ-cong {α , t̂} {α , t̂} (≈lstage α ≡.refl) x = ≡→≈ (Colim D) ≡.refl
    -- -- --   ϕ-cong {α , t̂} {β , û} (≈lstep p t̂) x = ≈lstep p (t̂ (lift x))
    -- -- --   ϕ-cong {α , t̂} {β , û} (≈lsym p) x = ≈lsym (ϕ-cong p x)
    -- -- --   ϕ-cong {α , t̂} {β , û} (≈ltrans p q) x = ≈ltrans (ϕ-cong p x) (ϕ-cong q x)

    -- -- --   ϕ : Colim/≈ D^X → (X → Colim/≈ D)
    -- -- --   ϕ f̃ x = ColimD^X.map (Colim D) (λ f → ϕ₀ f x) (λ p → ϕ-cong p x) f̃

    -- -- --   module _ {α β : Z} (α≤β : α ≤ β) where
    -- -- --     module Bα = Bounded D α
    -- -- --     module Bβ = Bounded D β

    -- -- --     map≤₀ : Bα.Colim≤₀ → Bβ.Colim≤₀
    -- -- --     map≤₀ (i≤α , x) = (i≤α .fst , ≤≤ α≤β (i≤α .snd)) , x

    -- -- --     map≈≤ : ∀ {s t} → Bα._≈ˡ≤_ s t → Bβ._≈ˡ≤_ (map≤₀ s) (map≤₀ t)
    -- -- --     map≈≤ (Bα.≈l≤stage ι e) = Bβ.≈l≤stage (ι .fst , ≤≤ α≤β (ι .snd)) e
    -- -- --     map≈≤ (Bα.≈l≤step p x) = Bβ.≈l≤step p x
    -- -- --     map≈≤ (Bα.≈l≤sym r) = Bβ.≈l≤sym (map≈≤ r)
    -- -- --     map≈≤ (Bα.≈l≤trans r₁ r₂) = Bβ.≈l≤trans (map≈≤ r₁) (map≈≤ r₂)

    -- -- -- --   module _ where
    -- -- -- --     open Bounded D renaming (_≈ˡ≤_ to _⊢_≈ˡ≤_)
    -- -- -- --     sameBounded : ∀ {γ α} (p q : α ≤ γ) {y : D̃ α /≈}
    -- -- -- --       → γ ⊢ ((α , p) , y) ≈ˡ≤ ((α , q) , y)
    -- -- -- --     sameBounded {γ} {α} p q {y} = B.≈l≤trans (B.≈l≤step (≤refl α) y) (B.≈l≤stage (α , q) eq)
    -- -- -- --       where
    -- -- -- --       module B = Bounded D γ
    -- -- -- --       module Dα = SetoidQuotient (D̃ α)
    -- -- -- --       module D∣γ = Functor (RestrictDiagram D γ)
    -- -- -- --       hom-refl : (y : D̃ α /≈) → D∣γ.hom {α , p} {α , p} (box (≤refl α)) y ≡ y
    -- -- -- --       hom-refl = Dα.elimp (λ y → D∣γ.hom {α , p} {α , p} (box (≤refl α)) y ≡ y) h
    -- -- -- --         where
    -- -- -- --         h : ∀ t̂ → D/≈.hom (box (≤refl α)) (D̃ α ⊢[ t̂ ]) ≡ D̃ α ⊢[ t̂ ]
    -- -- -- --         h t̂ rewrite rec-beta (D̃ α) (λ x → D̃ α ⊢[ pweaken (≤refl α) x ]) (λ {x y} p → D̃ α ⊢≈[ p ]) t̂ =
    -- -- -- --           D̃ α ⊢≈[ ≈trefl ]
    -- -- -- --       eq : D∣γ.hom {α , p} {α , p} (box (≤refl α)) y ≡ y
    -- -- -- --       eq = hom-refl y

    -- -- -- --     record BoundedJoin (x y : Colim₀ D) : Set (ℓA ⊔ ℓS ⊔ ℓP ⊔ lsuc ℓV ⊔ ℓE) where
    -- -- -- --       constructor bjoin
    -- -- -- --       private
    -- -- -- --         α = x .proj₁
    -- -- -- --         β = y .proj₁
    -- -- -- --         s̃ = x .proj₂
    -- -- -- --         t̃ = y .proj₂
    -- -- -- --       field
    -- -- -- --         γ : Z
    -- -- -- --         α≤γ : α ≤ γ
    -- -- -- --         β≤γ : β ≤ γ
    -- -- -- --         γ⊢x≈y : γ ⊢ ((α , α≤γ) , s̃) ≈ˡ≤ ((β , β≤γ) , t̃)

    -- -- -- --     boundedJoin : ∀ {α β} {x : D̃ α /≈} {y : D̃ β /≈}
    -- -- -- --       → Colim D [ α , x ≈ β , y ]
    -- -- -- --       → ∥ BoundedJoin (α , x) (β , y) ∥
    -- -- -- --     boundedJoin = recˡ D C sC pC syC trC
    -- -- -- --       where
    -- -- -- --       C : ∀ {s t} → Colim D [ s ≈ t ] → Prop _
    -- -- -- --       C {α , x} {β , y} _ = ∥ BoundedJoin (α , x) (β , y) ∥

    -- -- -- --       sC : ∀ α {x x'} (e : x ≡ x') → C (≈lstage α e)
    -- -- -- --       sC α e = ∣ bjoin α (≤refl α) (≤refl α) (≈l≤stage (α , ≤refl α) e) ∣

    -- -- -- --       pC : ∀ {α β} (p : α ≤ β) (x : D̃ α /≈) → C (≈lstep p x)
    -- -- -- --       pC {α} {β} p x = ∣ bjoin β p (≤refl β) (≈l≤step p x) ∣

    -- -- -- --       syC : ∀ {s t} (r : Colim D [ s ≈ t ]) → C r → C (≈lsym r)
    -- -- -- --       syC {α , x} {β , y} r ∣ bjoin γ α≤γ β≤γ γ⊢x≈y ∣ = ∣ bjoin γ β≤γ α≤γ (≈l≤sym γ⊢x≈y) ∣

    -- -- -- --       trC : ∀ {s t u} (r₁ : Colim D [ s ≈ t ]) (r₂ : Colim D [ t ≈ u ]) → C r₁ → C r₂ → C (≈ltrans r₁ r₂)
    -- -- -- --       trC {α , x} {β , y} {δ , z} r₁ r₂
    -- -- -- --           ∣ bjoin γ₁ α≤γ₁ β≤γ₁ γ₁⊢x≈y ∣
    -- -- -- --           ∣ bjoin γ₂ β≤γ₂ δ≤γ₂ γ₂⊢y≈z ∣ =
    -- -- -- --         ∣ bjoin γ α≤γ δ≤γ (≈l≤trans γ⊢x≈y (≈l≤trans γ⊢y≈y γ⊢y≈z)) ∣
    -- -- -- --         where
    -- -- -- --         γ : Z
    -- -- -- --         γ = γ₁ ∨ᶻ γ₂

    -- -- -- --         α≤γ : α ≤ γ
    -- -- -- --         α≤γ = ≤≤ ∨ᶻ-l α≤γ₁

    -- -- -- --         δ≤γ : δ ≤ γ
    -- -- -- --         δ≤γ = ≤≤ ∨ᶻ-r δ≤γ₂

    -- -- -- --         β≤γˡ : β ≤ γ
    -- -- -- --         β≤γˡ = ≤≤ ∨ᶻ-l β≤γ₁

    -- -- -- --         β≤γʳ : β ≤ γ
    -- -- -- --         β≤γʳ = ≤≤ ∨ᶻ-r β≤γ₂

    -- -- -- --         γ⊢x≈y : γ ⊢ ((α , α≤γ) , x) ≈ˡ≤ ((β , β≤γˡ) , y)
    -- -- -- --         γ⊢x≈y = map≈≤ ∨ᶻ-l γ₁⊢x≈y

    -- -- -- --         γ⊢y≈z : γ ⊢ ((β , β≤γʳ) , y) ≈ˡ≤ ((δ , δ≤γ) , z)
    -- -- -- --         γ⊢y≈z = map≈≤ ∨ᶻ-r γ₂⊢y≈z

    -- -- -- --         γ⊢y≈y : γ ⊢ ((β , β≤γˡ) , y) ≈ˡ≤ ((β , β≤γʳ) , y)
    -- -- -- --         γ⊢y≈y = sameBounded β≤γˡ β≤γʳ

    -- -- -- --     rankColim : ∀ {γ δ} {x : D̃ γ /≈} {y : D̃ δ /≈}
    -- -- -- --               → Colim D [ γ , x ≈ δ , y ] → rankD x ≡ rankD y
    -- -- -- --     rankColim (≈lstage i e) = ≡.cong rankD e
    -- -- -- --     rankColim (≈lstep {i = γ} p x) =
    -- -- -- --       elimp (D̃ γ)
    -- -- -- --             (λ q → rankD q ≡ rankD (D/≈.hom (box p) q))
    -- -- -- --             (rankD-step p)
    -- -- -- --             x
    -- -- -- --     rankColim (≈lsym p) = ≡.sym (rankColim p)
    -- -- -- --     rankColim (≈ltrans p q) = ≡.trans (rankColim p) (rankColim q)

    -- -- -- --     sameHom : ∀ {α γ} (p q : α ≤ γ) {x : D̃ α /≈}
    -- -- -- --             → D.hom (box p) x ≡ D.hom (box q) x
    -- -- -- --     sameHom {α} {γ} p q {x} = Dα.elimp B h x
    -- -- -- --       where
    -- -- -- --       module Dα = SetoidQuotient (D̃ α)
    -- -- -- --       B : D̃ α /≈ → Prop _
    -- -- -- --       B x = D.hom (box p) x ≡ D.hom (box q) x
    -- -- -- --       h : ∀ û → B (D̃ α ⊢[ û ])
    -- -- -- --       h û@(t , t≤α) =
    -- -- -- --         ≡.trans (hom-beta p û)
    -- -- -- --           (≡.trans (D̃ γ ⊢≈[ ≈trefl ])
    -- -- -- --             (≡.sym (hom-beta q û)))

    -- -- -- --     rankD≤stage : ∀ {α} (x : D̃ α /≈) → rankD x ≤ α
    -- -- -- --     rankD≤stage {α} = elimp (D̃ α) (λ x → rankD x ≤ α)
    -- -- -- --       (λ û@(t , t≤α) → ≡.substp (_≤ α) (≡.sym (rankD-beta û)) t≤α)

    -- -- -- --     toRankHom : ∀ {α} (x : D̃ α /≈) → ∀ {γ} (α≤γ : α ≤ γ)
    -- -- -- --               → D.hom (box α≤γ) x
    -- -- -- --               ≡ D.hom (box (≤≤ α≤γ (rankD≤stage x))) (plift≈ x)
    -- -- -- --     toRankHom {α} x {γ} α≤γ = elimp (D̃ α) Q u x 
    -- -- -- --       where
    -- -- -- --       open ≡.≡-Reasoning
    -- -- -- --       Q : ∀ x → Prop _
    -- -- -- --       Q x = D/≈.hom (box α≤γ) x
    -- -- -- --           ≡ D/≈.hom (box (≤≤ α≤γ (rankD≤stage x))) (plift≈ x)
    -- -- -- --       u : (t : D₀ α) → Q (D̃ α ⊢[ t ])
    -- -- -- --       u t =
    -- -- -- --         D.hom (box α≤γ) (D̃ α ⊢[ t ])
    -- -- -- --           ≡⟨ D/≈.hom-beta (box α≤γ) t ⟩
    -- -- -- --         D̃ γ ⊢[ pweaken α≤γ t ]
    -- -- -- --           ≡⟨ {!!} ⟩
    -- -- -- --         D.hom (box (≤≤ α≤γ (rankD≤stage (D̃ α ⊢[ t ])))) (subst D̃/≈ (≡.sym (rankD-beta t)) (plift₀ t))
    -- -- -- --           ≡⟨ ≡.cong (D.hom (box (≤≤ α≤γ (rankD≤stage (D̃ α ⊢[ t ]))))) (≡.sym {!plift-beta!}) ⟩
    -- -- -- --         D.hom (box (≤≤ α≤γ (rankD≤stage (D̃ α ⊢[ t ])))) (plift≈ (D̃ α ⊢[ t ])) ∎

    -- -- -- --     postulate
    -- -- -- --       joinRank : ∀ {α β} {x : D̃ α /≈} {y : D̃ β /≈}
    -- -- -- --               → Colim D [ α , x ≈ β , y ]
    -- -- -- --               → ∀ {γ} (rx≤γ : rankD x ≤ γ) (ry≤γ : rankD y ≤ γ)
    -- -- -- --               → D.hom (box rx≤γ) (plift≈ x) ≡ D.hom (box ry≤γ) (plift≈ y)

    -- -- -- --       join≈ : ∀ {α β} {x : D̃ α /≈} {y : D̃ β /≈}
    -- -- -- --             → Colim D [ α , x ≈ β , y ]
    -- -- -- --             → ∀ {γ} (α≤γ : α ≤ γ) (β≤γ : β ≤ γ)
    -- -- -- --             → D.hom (box α≤γ) x ≡ D.hom (box β≤γ) y

    -- -- -- --   ϕ-inj≈ : ∀ {t̃ ũ} → (∀ x → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ])
    -- -- -- --         → Colim D^X [ t̃ ≈ ũ ]
    -- -- -- --   ϕ-inj≈ {α , t̂} {β , û} p =
    -- -- -- --       α , t̂
    -- -- -- --     ≈⟨ ≈lstep ∨ᶻ-l t̂ ⟩
    -- -- -- --       γ , (λ x → D.hom (box ∨ᶻ-l) (t̂ x))
    -- -- -- --     ≈⟨ ≈lstage (α ∨ᶻ β) (≡.funExt q) ⟩
    -- -- -- --       γ , (λ x → D.hom (box ∨ᶻ-r) (û x))
    -- -- -- --     ≈⟨ ≈lsym (≈lstep ∨ᶻ-r û) ⟩
    -- -- -- --       β , û ∎
    -- -- -- --     where
    -- -- -- --     open ≈.≈syntax {S = Colim D^X}
    -- -- -- --     γ : Z
    -- -- -- --     γ = α ∨ᶻ β
    -- -- -- --     q : ∀ x → D.hom (box ∨ᶻ-l) (t̂ x) ≡ D.hom (box ∨ᶻ-r) (û x)
    -- -- -- --     q x = join≈ (p (lower x)) ∨ᶻ-l ∨ᶻ-r

    -- -- -- --   ϕ-β : ∀ t̃ x → ϕ (ColimD^X.[ t̃ ]) x ≡ ColimD.[ ϕ₀ t̃ x ]
    -- -- -- --   ϕ-β t̃ x = ≡.trans
    -- -- -- --     (ColimD^X.rec-beta
    -- -- -- --       (λ f̃ → Q.[ ϕ₀ f̃ x ])
    -- -- -- --       (λ p → Q.quot-rel _ _ (ϕ-cong p x))
    -- -- -- --       t̃)
    -- -- -- --     (≡.sym (ColimD.[]-beta (ϕ₀ t̃ x)))

    -- -- -- --   ϕ-inj : ∀ {t̃ ũ} → (∀ x → ϕ t̃ x ≡ ϕ ũ x) → t̃ ≡ ũ
    -- -- -- --   ϕ-inj {t̃} {ũ} = ColimD^X.elimp₂ {B = λ t̃ ũ → (∀ x → ϕ t̃ x ≡ ϕ ũ x) → t̃ ≡ ũ} step t̃ ũ
    -- -- -- --     where
    -- -- -- --     step : ∀ t̃ ũ → (∀ x → ϕ (ColimD^X.[ t̃ ]) x ≡ ϕ (ColimD^X.[ ũ ]) x) → ColimD^X.[ t̃ ] ≡ ColimD^X.[ ũ ]
    -- -- -- --     step t̃ ũ p = ColimD^X.≈[ ϕ-inj≈ q ]
    -- -- -- --       where
    -- -- -- --       q : ∀ x → Colim D [ ϕ₀ t̃ x ≈ ϕ₀ ũ x ]
    -- -- -- --       q x = ColimD.effectiveness _ _ eq
    -- -- -- --         where
    -- -- -- --         eq : ColimD.[ ϕ₀ t̃ x ] ≡ ColimD.[ ϕ₀ ũ x ]
    -- -- -- --         eq = ≡.trans (≡.sym (ϕ-β t̃ x)) (≡.trans (p x) (ϕ-β ũ x))

    -- -- -- --   ϕ-surj≈ : (f̂ : X → Colim₀ D) → ∃ λ t̂ → ∀ x → Colim D [ ϕ₀ t̂ x ≈ f̂ x ]
    -- -- -- --   ϕ-surj≈ f̂ = ∣ t̂ , p ∣
    -- -- -- --     where
    -- -- -- --     α : Z
    -- -- -- --     α = Z.sup (ιˢ s , λ x → f̂ x .proj₁)
    -- -- -- --     t̂ : Colim₀ D^X
    -- -- -- --     t̂ = α , (λ (lift x) → D.hom (box (child≤ s _ x)) (proj₂ (f̂ x)))
    -- -- -- --     p : ∀ x → Colim D [ ϕ₀ t̂ x ≈ f̂ x ]
    -- -- -- --     p x = sym (≈lstep β≤α (proj₂ (f̂ x)))
    -- -- -- --       where
    -- -- -- --       β : Z
    -- -- -- --       β = f̂ x .proj₁
    -- -- -- --       β≤α : β ≤ α
    -- -- -- --       β≤α = child≤ s _ x
    -- -- -- --       open ≈.≈syntax {S = Colim D}
    -- -- -- --       open Setoid (Colim D)

    -- -- -- --   sect : Colim/≈ D → Colim₀ D
    -- -- -- --   sect = ColimD.rec sect₀ stable
    -- -- -- --     where
    -- -- -- --     sect₀ : Colim₀ D → Colim₀ D
    -- -- -- --     sect₀ (α , s̃) = rankD s̃ , plift≈ s̃
    -- -- -- --     sect-hom : ∀ {α β} → (p : α ≤ β) → (s̃ : D̃ α /≈) → sect₀ (α , s̃) ≡ sect₀ (β , D.hom (box p) s̃)
    -- -- -- --     sect-hom {α} {β} p s̃ =
    -- -- -- --       rankD s̃ , plift≈ s̃
    -- -- -- --         ≡⟨ ≡.Σ≡ (rankD-hom s̃) (plift≈-hom s̃ (rankD-hom s̃)) ⟩
    -- -- -- --       rankD (D.hom (box p) s̃) , plift≈ (D.hom (box p) s̃) ∎
    -- -- -- --       where
    -- -- -- --       open ≡.≡-Reasoning
    -- -- -- --       rankD-hom : ∀ (s̃ : D̃ α /≈) → rankD s̃ ≡ rankD (D.hom (box p) s̃)
    -- -- -- --       rankD-hom = elimp (D̃ α) (λ s̃ → rankD s̃ ≡ rankD (D.hom (box p) s̃)) (rankD-step p)
    -- -- -- --       plift≈-hom : ∀ (s̃ : D̃ α /≈)
    -- -- -- --                 → (q : rankD s̃ ≡ rankD (D.hom (box p) s̃))
    -- -- -- --                 → subst D̃/≈ (rankD-hom s̃) (plift≈ s̃) ≡ (plift≈ (D.hom (box p) s̃))
    -- -- -- --       plift≈-hom = elimp (D̃ α) _ r
    -- -- -- --         where
    -- -- -- --         r : (a : D₀ α)
    -- -- -- --           → (q : rankD (D̃ α ⊢[ a ]) ≡ rankD (D.hom (box p) (D̃ α ⊢[ a ]))) 
    -- -- -- --           → subst D̃/≈ q (plift≈ (D̃ α ⊢[ a ]))
    -- -- -- --           ≡ plift≈ (D.hom (box p) (D̃ α ⊢[ a ]))
    -- -- -- --         r a q =
    -- -- -- --           subst D̃/≈ q (plift≈ (D̃ α ⊢[ a ]))
    -- -- -- --             ≡⟨ ≡.cong (subst D̃/≈ q)
    -- -- -- --                       (elim-beta (D̃ α) (λ t̂ → D̃/≈ (rankD t̂)) {!!} {!!} {!!}) ⟩
    -- -- -- --           subst D̃/≈ q {!!}
    -- -- -- --             ≡⟨ {!!} ⟩
    -- -- -- --           plift≈ (D.hom (box p) (D̃ α ⊢[ a ])) ∎
              
    -- -- -- --     stable : ∀ {x y} → Colim D [ x ≈ y ] → sect₀ x ≡ sect₀ y
    -- -- -- --     stable {α , s̃} {α , t̃} (≈lstage α ≡.refl) = ≡.refl
    -- -- -- --     stable {α , s̃} {β , t̃} (≈lstep p s̃) = sect-hom p s̃
    -- -- -- --     stable {α , s̃} {β , t̃} (≈lsym p) = ≡.sym (stable p)
    -- -- -- --     stable {α , s̃} {β , t̃} (≈ltrans p q) = ≡.trans (stable p) (stable q)

    -- -- -- -- --   isSectionSect : ∀ x → Colim D ⊢[ sect x ] ≡ x
    -- -- -- -- --   isSectionSect = elimp (Colim D) (λ z → (Colim D ⊢[ sect z ]) ≡ z) u
    -- -- -- -- --     where
    -- -- -- -- --     u : ∀ x → Colim D ⊢[ sect ColimD.[ x ] ] ≡ ColimD.[ x ]
    -- -- -- -- --     u (α , s̃) = Colim D ⊢≈[ p ]
    -- -- -- -- --       where
    -- -- -- -- --       rankD≤α : rankD s̃ ≤ α
    -- -- -- -- --       rankD≤α = rankD≤stage s̃

    -- -- -- -- --       weakenPlift≈ : D.hom (box rankD≤α) (plift≈ s̃) ≡ s̃
    -- -- -- -- --       weakenPlift≈ =
    -- -- -- -- --         ≡.trans
    -- -- -- -- --           (sameHom rankD≤α (≤≤ (≤refl α) rankD≤α) {x = plift≈ s̃})
    -- -- -- -- --           (≡.trans
    -- -- -- -- --             (≡.sym (toRankHom s̃ (≤refl α)))
    -- -- -- -- --             (D.id {x = α} {s̃}))

    -- -- -- -- --       p : Colim D [ (rankD s̃ , plift≈ s̃) ≈ (α , s̃) ]
    -- -- -- -- --       p =
    -- -- -- -- --         rankD s̃ , plift≈ s̃
    -- -- -- -- --           ≈⟨ ≈lstep rankD≤α (plift≈ s̃) ⟩
    -- -- -- -- --         α , D.hom (box rankD≤α) (plift≈ s̃)
    -- -- -- -- --           ≈⟨ ≈lstage α weakenPlift≈ ⟩
    -- -- -- -- --         α , s̃ ∎
    -- -- -- -- --         where
    -- -- -- -- --         open ≈.≈syntax {S = Colim D}
    -- -- -- -- --         open Setoid (Colim D)

    -- -- -- -- --   ϕ-surj : (f : X → Colim/≈ D) → ∃ λ t̃ → ϕ t̃ ≡ f
    -- -- -- -- --   ϕ-surj f = helper (ϕ-surj≈ f₀)
    -- -- -- -- --     where
    -- -- -- -- --     f₀ : X → Colim₀ D
    -- -- -- -- --     f₀ x = sect (f x)

    -- -- -- -- --     helper : (∃ λ t̂ → ∀ x → Colim D [ ϕ₀ t̂ x ≈ f₀ x ])
    -- -- -- -- --           → ∃ λ t̃ → ϕ t̃ ≡ f
    -- -- -- -- --     helper ∣ t̂ , p ∣ = ∣ Colim D^X ⊢[ t̂ ] , ≡.funExt h ∣
    -- -- -- -- --       where
    -- -- -- -- --       h : ∀ x → ϕ (Colim D^X ⊢[ t̂ ]) x ≡ f x
    -- -- -- -- --       h x = ≡.trans (ϕ-β t̂ x)
    -- -- -- -- --               (≡.trans (Colim D ⊢≈[ p x ])
    -- -- -- -- --                         (isSectionSect (f x)))

    -- -- -- -- --   iso : Iso (Colim/≈ D^X) (X → Colim/≈ D)
    -- -- -- -- --   iso = Bijection→Iso a!c ϕ ((λ p → ϕ-inj (≡.funExt⁻ p)) , ϕ-surj)

    -- -- -- -- --   ψ : (X → Colim/≈ D) → Colim/≈ D^X
    -- -- -- -- --   ψ = f⁻¹
    -- -- -- -- --     where
    -- -- -- -- --     open Iso iso

    -- -- -- -- --   ϕψ-sect : ∀ {x} → ψ (ϕ x) ≡ x
    -- -- -- -- --   ϕψ-sect = linv
    -- -- -- -- --     where
    -- -- -- -- --     open Iso iso

    -- -- -- -- --   ϕψ-retr : ∀ {x} → ϕ (ψ x) ≡ x
    -- -- -- -- --   ϕψ-retr = rinv
    -- -- -- -- --     where
    -- -- -- -- --     open Iso iso

    -- -- -- -- -- module Pow = PreservationByPowers

    -- -- -- -- -- ϕ₀ : Colim₀ (F ∘ D) → F.ob (Colim/≈ D)
    -- -- -- -- -- ϕ₀ (α , (s , ũ)) =
    -- -- -- -- --   s , Pow.ϕ s (Colim (Pow.D^X s) ⊢[ α , (λ (lift z) → ũ z) ])
    -- -- -- -- -- ϕ-cong : ∀ {x y} → Colim (F ∘ D) [ x ≈ y ] → ϕ₀ x ≡ ϕ₀ y
    -- -- -- -- -- ϕ-cong {α , a , x} {α , b , y} (≈lstage α ≡.refl) = ≡.refl
    -- -- -- -- -- ϕ-cong {α , a , x} {β , a , y} (≈lstep p (a , x)) =
    -- -- -- -- --   ≡.cong (a ,_) u
    -- -- -- -- --   where
    -- -- -- -- --   open Pow a
    -- -- -- -- --   module Pa = Pow a
    -- -- -- -- --   open ≡.≡-Reasoning
    -- -- -- -- --   u : Pa.ϕ (ColimD^X.[ α , (λ i → x (i .lower)) ])
    -- -- -- -- --     ≡ Pa.ϕ (ColimD^X.[ β , (λ i → D.hom (box p) (x (i .lower))) ])
    -- -- -- -- --   u = ≡.cong Pa.ϕ (Colim D^X ⊢≈[ ≈lstep p (λ z → x (z .lower)) ])
    -- -- -- -- -- ϕ-cong {α , a , x} {β , b , y} (≈lsym p) = ≡.sym (ϕ-cong p)
    -- -- -- -- -- ϕ-cong {α , a , x} {β , b , y} (≈ltrans p q) = ≡.trans (ϕ-cong p) (ϕ-cong q)

    -- -- -- -- -- ϕ : Colim/≈ (F ∘ D) → F.ob (Colim/≈ D)
    -- -- -- -- -- ϕ = rec (Colim (F ∘ D)) ϕ₀ ϕ-cong

    -- -- -- -- -- module _ (s : S) where
    -- -- -- -- --   open Pow s
    -- -- -- -- --   inS₀ : Colim₀ D^X → Colim/≈ (F ∘ D)
    -- -- -- -- --   inS₀ (α , f̃) = ColimF∘D.[ α , s , (λ z → f̃ (lift z)) ]
    -- -- -- -- --   inS-cong : ∀ {x y} → Colim D^X [ x ≈ y ] → inS₀ x ≡ inS₀ y
    -- -- -- -- --   inS-cong (≈lstage α ≡.refl) = ≡.refl
    -- -- -- -- --   inS-cong (≈lstep p f̃) = ColimF∘D.≈[ ≈lstep p _ ]
    -- -- -- -- --   inS-cong (≈lsym p) = ≡.sym (inS-cong p)
    -- -- -- -- --   inS-cong (≈ltrans p p₁) = ≡.trans (inS-cong p) (inS-cong p₁)

    -- -- -- -- --   inS : Colim/≈ (Pow.D^X s) → Colim/≈ (F ∘ D)
    -- -- -- -- --   inS = rec (Colim (Pow.D^X s)) inS₀ inS-cong

    -- -- -- -- -- ϕinS : ∀ s (q : Colim/≈ (Pow.D^X s)) → ϕ (inS s q) ≡ (s , Pow.ϕ s q)
    -- -- -- -- -- ϕinS s = ColimPow.elimp B h
    -- -- -- -- --   where
    -- -- -- -- --   module Ps = Pow s
    -- -- -- -- --   module ColimPow = SetoidQuotient (Colim (Ps.D^X))

    -- -- -- -- --   B : Colim/≈ (Ps.D^X) → Prop _
    -- -- -- -- --   B q = ϕ (inS s q) ≡ (s , Ps.ϕ q)

    -- -- -- -- --   h : ∀ t̂ → B (ColimPow.[ t̂ ])
    -- -- -- -- --   h t̂ =
    -- -- -- -- --     ≡.trans
    -- -- -- -- --       (≡.cong ϕ (ColimPow.rec-beta (inS₀ s) (inS-cong s) t̂))
    -- -- -- -- --       (ColimF∘D.rec-beta ϕ₀ ϕ-cong (α , (s , λ z → f̃ (lift z))))
    -- -- -- -- --     where
    -- -- -- -- --     α = t̂ .proj₁
    -- -- -- -- --     f̃ = t̂ .proj₂

    -- -- -- -- -- ψ : F.ob (Colim/≈ D) → Colim/≈ (F ∘ D)
    -- -- -- -- -- ψ (s , f̃) = inS s (Pow.ψ s f̃)

    -- -- -- -- -- cocontinuous : Iso (Colim/≈ (F ∘ D)) (Functor.ob F (Colim/≈ D))
    -- -- -- -- -- cocontinuous = record
    -- -- -- -- --   { f = ϕ
    -- -- -- -- --   ; f⁻¹ = ψ
    -- -- -- -- --   ; linv = linv
    -- -- -- -- --   ; rinv = rinv }
    -- -- -- -- --   where
    -- -- -- -- --   linv : ∀ {x} → ψ (ϕ x) ≡ x
    -- -- -- -- --   linv {x} = elimp (Colim (F ∘ D)) (λ x → ψ (ϕ x) ≡ x) p x
    -- -- -- -- --     where
    -- -- -- -- --     open ≡.≡-Reasoning
    -- -- -- -- --     p : ∀ x → ψ (ϕ ColimF∘D.[ x ]) ≡ ColimF∘D.[ x ]
    -- -- -- -- --     p (α , (s , ũ)) =
    -- -- -- -- --       ψ (ϕ ColimF∘D.[ (α , (s , ũ)) ])
    -- -- -- -- --         ≡⟨ ≡.refl ⟩
    -- -- -- -- --       ψ (ϕ₀ (α , (s , ũ)))
    -- -- -- -- --         ≡⟨ ≡.refl ⟩
    -- -- -- -- --       ψ (s , Pow.ϕ s (Colim (Pow.D^X s) ⊢[ α , (λ (lift z) → ũ z) ]))
    -- -- -- -- --         ≡⟨ ≡.refl ⟩
    -- -- -- -- --       inS s (Pow.ψ s (Pow.ϕ s (Colim (Pow.D^X s) ⊢[ α , (λ (lift z) → ũ z) ])))
    -- -- -- -- --         ≡⟨ ≡.cong (inS s)
    -- -- -- -- --                   (Pow.ϕψ-sect s {Colim (Pow.D^X s) ⊢[ α , (λ (lift z) → ũ z) ]}) ⟩
    -- -- -- -- --       inS s (Colim (Pow.D^X s) ⊢[ α , (λ (lift z) → ũ z) ])
    -- -- -- -- --         ≡⟨ ≡.refl ⟩
    -- -- -- -- --       inS₀ s (α , λ (lift z) → ũ z)
    -- -- -- -- --         ≡⟨ ≡.refl ⟩
    -- -- -- -- --       ColimF∘D.[ (α , (s , ũ)) ] ∎
    -- -- -- -- --   rinv : ∀ {x} → ϕ (ψ x) ≡ x
    -- -- -- -- --   rinv {s , f̃} =
    -- -- -- -- --     ≡.trans
    -- -- -- -- --       (ϕinS s (Pow.ψ s f̃))
    -- -- -- -- --       (≡.cong (s ,_) (Pow.ϕψ-retr s {f̃}))
