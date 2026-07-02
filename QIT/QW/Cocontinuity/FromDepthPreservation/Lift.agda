open import QIT.QW.Cocontinuity.FromDepthPreservation.Prelude

module QIT.QW.Cocontinuity.FromDepthPreservation.Lift
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (ℓA : Level)
  ⦃ depthPreserving* : DepthPreservingSig sig ⦄
  ⦃ extensionalPlumpOrdinals* : ExtensionalPlumpOrdinals sig ℓA ⦄
  (s : sig .Sig.S)
  where

open import QIT.QW.Cocontinuity.FromDepthPreservation.DepthPreserving sig ℓA
open import QIT.QW.Cocontinuity.FromDepthPreservation.Rank sig ℓA

open import QIT.QW.Subclasses sig hiding (DepthPreservingSig)

open Sig sig
open A!C a!c*
open FunExt funExt*
open ExtensionalPlumpOrdinals extensionalPlumpOrdinals*

open import QIT.QW.StageColimit sig Zᴬ

open import QIT.Plump.Properties Zᴬ
open import QIT.Setoid.Properties

open import QIT.QW.Algebra sig
-- open import QIT.QW.Colimit ≤p ℓD ℓD' hiding (_≈ˡ_)

private
  ℓc = ℓA ⊔ ℓS ⊔ ℓP
  ℓc' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV

open import QIT.Container.Base
open import QIT.Functor.Properties renaming (_∘_ to _∘ꟳ_)
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))
open import QIT.Setoid.Quotient
open import QIT.QW.Equation
open import QIT.QW.Colimit.Base ≤p ℓc ℓc'
open import QIT.Container.Properties 

open SQ

plift : ∀ {α} → (t̂ : D₀ α) → D₀ (rankD₀ t̂)
plift (t , _) = t , ≤refl (ιᶻ t)

plift₀ : ∀ {α} → (t̂ : D₀ α) → D̃ (rankD₀ t̂) /≈
plift₀ {α} (t , t≤α) = D̃ (ιᶻ t) ⊢[ t , ≤refl _ ]

open ≡.≡-Reasoning

plift-fst : ∀ {γ} (û : D₀ γ) → plift û .fst ≡ û .fst
plift-fst û = ≡.refl

plift-psup : ∀ a μ (f : ∀ i → D₀ (μ i))
  → plift (psup a μ f) ≡ psup a (λ i → rankD₀ (f i)) (λ i → plift (f i))
plift-psup a μ f = ΣP≡ _ _ ≡.refl

-- exactify : ∀ {γ} {ŝ t̂ : D₀ γ} (p : D̃ γ [ ŝ ≈ t̂ ])
--   → D̃ (rankD₀ ŝ) [ plift ŝ ≈ subst D₀ (≡.sym (rankD-cong p)) (plift t̂) ]
-- exactify (≈pcong a μ f₁ g r) = castˡ (plift-psup a μ f₁) (castʳ rhs≈ base)
--   where
--   δi : ∀ i → rankD₀ (f₁ i) ≡ rankD₀ (g i)
--   δi i = rankD-cong (r i)
--   μ' : P a → Z
--   μ' i = rankD₀ (f₁ i)
--   f' : ∀ i → D₀ (μ' i)
--   f' i = plift (f₁ i)
--   g' : ∀ i → D₀ (μ' i)
--   g' i = subst D₀ (≡.sym (δi i)) (plift (g i))
--   base : D̃ (rankD₀ (psup a μ f₁)) [ psup a μ' f' ≈ psup a μ' g' ]
--   base = ≈pcong a μ' f' g' (λ i → exactify (r i))
--   dp' : rankD₀ (psup a μ f₁) ≡ rankD₀ (psup a μ g)
--   dp' = rankD-cong (≈pcong a μ f₁ g r)
--   g'fst : ∀ i → (g' i) .fst ≡ (plift (g i)) .fst
--   g'fst i = {!subst-D₀-fst (≡.sym (δi i)) (plift (g i))!}
--   rhs≈ : psup a μ' g' ≡ subst D₀ (≡.sym dp) (plift (psup a μ g))
--   rhs≈ = ΣP≡ _ _ rhsfst
--     where
--     rhsfst : (psup a μ' g') .fst ≡ (subst D₀ (≡.sym dp) (plift (psup a μ g))) .fst
--     -- rhsfst = ≡.trans (≡.cong (λ h → W.sup (a , h)) (funExt g'fst))
--     --                   (≡.sym (subst-D₀-fst (≡.sym dp) (plift (psup a μ g))))
-- exactify (≈psat e ϕ l≤α r≤α) = castʳ rhs≈ base
--   where
--   dp' : rankD₀ (lhs' e ϕ , l≤α) ≡ rankD₀ (rhs' e ϕ , r≤α)
--   dp' = rankD-cong (≈psat e ϕ l≤α r≤α)
--   base : D̃ (rankD₀ (lhs' e ϕ , l≤α)) [ plift (lhs' e ϕ , l≤α) ≈ (rhs' e ϕ , ≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _)) ]
--   base = ≈psat e ϕ (≤refl _) (≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _))
--   rhs≈ : (rhs' e ϕ , ≡.substp (rhs' e ϕ ≤ᵀ_) (≡.sym dp) (≤refl _)) ≡ subst D₀ (≡.sym dp) (plift (rhs' e ϕ , r≤α))
--   rhs≈ = ΣP≡ _ _ (≡.sym (subst-D₀-fst (≡.sym dp) (plift (rhs' e ϕ , r≤α))))
-- exactify ≈prefl = ≈prefl
-- exactify {ŝ = ŝ} {t̂ = t̂} (≈psym p) =
--   castˡ {z = subst D₀ dp (plift t̂)} lhs≈ (transport≈ dp (≈psym (exactify p)))
--   where
--   dp : rankD₀ t̂ ≡ rankD₀ ŝ
--   dp = rankD-cong p
--   lhs≈ : subst D₀ dp (subst D₀ (≡.sym dp) (plift ŝ)) ≡ plift ŝ
--   lhs≈ = ≡.subst-inv D₀ (≡.sym dp)
-- exactify {ŝ = ŝ} {t̂ = û} (≈ptrans {ŝ = ŝ} {t̂ = t̂} {û = û} p q) = castʳ rhs≈ (≈ptrans (exactify p) mid)
--   where
--   dp : rankD₀ ŝ ≡ rankD₀ t̂
--   dp = rankD-cong p
--   dq : rankD₀ t̂ ≡ rankD₀ û
--   dq = rankD-cong q
--   mid : D̃ (rankD₀ ŝ) [ subst D₀ (≡.sym dp) (plift t̂) ≈ subst D₀ (≡.sym dp) (subst D₀ (≡.sym dq) (plift û)) ]
--   mid = transport≈ (≡.sym dp) (exactify q)
--   rhs≈ : subst D₀ (≡.sym dp) (subst D₀ (≡.sym dq) (plift û)) ≡ subst D₀ (≡.sym (rankD-cong (≈ptrans p q))) (plift û)
--   rhs≈ = ≡.subst-subst D₀ (≡.sym dq) (≡.sym dp) (plift û)
-- exactify (≈pweaken α≤β p) = exactify p

-- shiftRepresentative : ∀ {γ δ} {û : D₀ δ} (p : γ ≡ δ)
--   → subst (λ β → D̃ β /≈) p (D̃ γ ⊢[ subst D₀ (≡.sym p) û ])
--   ≡ D̃ δ ⊢[ û ]
-- shiftRepresentative ≡.refl = ≡.refl

-- plift₀-cong : ∀ {γ} {ŝ t̂ : D₀ γ} (p : D̃ γ [ ŝ ≈ t̂ ])
--   → subst D̃/≈ (rankD-cong p) (plift₀ ŝ) ≡ plift₀ t̂
-- plift₀-cong {ŝ = ŝ} {t̂ = t̂} p =
--   ≡.trans
--     (≡.cong (subst D̃/≈ (rankD-cong p)) (D̃ (rankD₀ ŝ) ⊢≈[ exactify p ]))
--     (shiftRepresentative (rankD-cong p))

-- plift≈ : ∀ {α} → (t̂ : D̃ α /≈) → D̃ (rankD t̂) /≈
-- plift≈ {α} = elim (D̃ α) (λ t̂ → D̃ (rankD t̂) /≈) u p
--   where
--   open ≡.≡-Reasoning
