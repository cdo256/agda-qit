open import QIT.Prelude hiding (ℓD; lift)
open import QIT.Prop
open import QIT.Types
open import QIT.Setoid
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Plump.Algebra
open import QIT.QW.Signature
open import QIT.QW.Subclasses using (DepthPreservingSig)
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Nullary
open import QIT.Relation.SetQuotient
open import QIT.Relation.Subset
open import QIT.Set.Bijection
open import QIT.Set.Base
open import QIT.Identity as Id using (dfunExtp)
open import QIT.Setoid.Quotient

module QIT.QW.Cocontinuity.FromDepthPreservation2
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  ⦃ depthPreserving* : DepthPreservingSig sig ⦄
  ⦃ epo* : ExtensionalPlumpOrdinals ⦄
  where

private
  ℓD = ℓS ⊔ ℓP
  ℓD' = ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV

open Sig sig
open FunExt funExt*
open DepthPreservingSig depthPreserving*
open ExtensionalPlumpOrdinals epo*
open ExtensionalPlumpAlgebra (Zᴬe S P) 

open import QIT.QW.Stage sig Zᴬ
open import QIT.QW.Diagram sig Zᴬ
import QIT.Plump.Extensional S P as Z
open Z using (ιᶻ; ιᶻ≤≥ιᶻ; child≤)

open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
open import QIT.Colimit Z.≤p ℓD ℓD'

module F = Functor F
module D̃ = Functor D̃
module D̃/ = Functor D̃/
module FD̃/ = Functor FD̃/
module D* = Setoid D*
module FD* = Setoid FD*
  
module DepthPreserving where
  dpᵗ : ∀ s t → s ≈ᵗ t → ιᶻ s ≡ ιᶻ t
  dpᵗ s t (≈tcong a f g r) =
    ≡.cong (λ ○ → Z.sup (a , ○))
            (funExt (λ i → dpᵗ (f i) (g i) (r i)))
  dpᵗ s t (≈tsat e ϕ) = 
    Z.≤≥→≡ (ιᶻ≤≥ιᶻ (lhs' e ϕ) (rhs' e ϕ)
                   (dpe e λ v → lower (ϕ v)))
  dpᵗ s t ≈trefl = ≡.refl
  dpᵗ s t (≈tsym p) = ≡.sym (dpᵗ t s p)
  dpᵗ s t (≈ttrans p q) = ≡.trans (dpᵗ s _ p) (dpᵗ _ t q)

  dp : ∀ {α β} (ŝ : S₀ α) (t̂ : S₀ β) → ŝ ≈ˢ t̂ → Z.ιᶻ (ŝ .fst) ≡ Z.ιᶻ (t̂ .fst)
  dp (s , _) (t , _) p = dpᵗ s t p

module Rank where
  open DepthPreserving

  rank₀ : ∀ {α} → S₀ α → Z
  rank₀ (t , _) = ιᶻ t

  rank₀-cong : ∀ {α β} (ŝ  : S₀ α) (t̂ : S₀ β) → ŝ ≈ˢ t̂ → rank₀ ŝ ≡ rank₀ t̂
  rank₀-cong ŝ t̂ p = dp ŝ t̂ p

  rank : ∀ {α} → S̃/ α → Z
  rank {α} = SQ.rec (S̃ α) rank₀ λ {ŝ t̂} → rank₀-cong ŝ t̂

  rank-beta : ∀ {α} (t̂ : S₀ α) → rank (S̃ α ⊢[ t̂ ]) ≡ rank₀ t̂
  rank-beta {α} t̂ = SQ.rec-beta (S̃ α) rank₀ (λ {ŝ t̂} → rank₀-cong ŝ t̂) t̂

  rank-cong : ∀ {α β} (ŝ  : S₀ α) (t̂ : S₀ β) → ŝ ≈ˢ t̂
            → rank (S̃ α ⊢[ ŝ ]) ≡ rank (S̃ β ⊢[ t̂ ])
  rank-cong ŝ t̂ p =
    substp₂ _≡_ (≡.sym (rank-beta ŝ))
                (≡.sym (rank-beta t̂))
                (dp ŝ t̂ p)

  rank₀≤ : ∀ {α} → (ŝ : S₀ α) → rank₀ ŝ ≤ α
  rank₀≤ {α} (s , s≤α) = s≤α

  rank≤ : ∀ {α} → (ŝ : S̃/ α) → rank ŝ ≤ α
  rank≤ {α} = SQ.elimp (S̃ α) (λ ŝ → rank ŝ ≤ α) p
    where
    p : ∀ ŝ → rank (S̃ α ⊢[ ŝ ]) ≤ α
    p ŝ = ≡.substp (_≤ α) (≡.sym (rank-beta ŝ)) (rank₀≤ ŝ)

  rankC₀ : D*₀ → Z
  rankC₀ (_ , t̂) = rank t̂

  rank-step₀ : ∀ {α β} (p : α ≤ β) (t̂ : S₀ α)
            → rank (S̃ α ⊢[ t̂ ]) ≡ rank (D̃/.hom (box p) (S̃ α ⊢[ t̂ ]))
  rank-step₀ p t̂ =
    ≡.trans (rank-beta t̂)
      (≡.trans (≡.sym (rank-beta (dweaken₀ p t̂)))
        (≡.cong rank (≡.sym (dweaken-beta p t̂))))

  rank-step : ∀ {α β} (p : α ≤ β) (t̂ : S̃/ α)
            → rank t̂ ≡ rank (D̃/.hom (box p) t̂)
  rank-step {α} p =
    SQ.elimp (S̃ α)
      (λ q → rank q ≡ rank (D̃/.hom (box p) q))
      (rank-step₀ p)

  rankC-cong : ∀ {x y} → D* [ x ≈ y ]
             → rankC₀ x ≡ rankC₀ y
  rankC-cong (≈lstage i p) = ≡.cong rank p
  rankC-cong (≈lstep p x) = rank-step p x
  rankC-cong (≈lsym p) =
    ≡.sym (rankC-cong p)
  rankC-cong (≈ltrans p q) =
    ≡.trans (rankC-cong p) (rankC-cong q)

  rankC : D*/ → Z
  rankC = SQ.rec D* rankC₀ rankC-cong

  rankC-beta : (x : D*₀) → rankC (D* ⊢[ x ]) ≡ rankC₀ x
  rankC-beta = SQ.rec-beta (D*) rankC₀ rankC-cong

  rankC-dp : ∀ {x y} → D* [ x ≈ y ]
           → rankC (D* ⊢[ x ]) ≡ rankC (D* ⊢[ y ])
  rankC-dp {x} {y} p =
    ≡.trans (rankC-beta x)
      (≡.trans (rankC-cong p)
        (≡.sym (rankC-beta y)))

module LiftElement where
  open DepthPreserving
  -- open SQ
  open Rank

  liftS₀ : ∀ {α β} → (t̂ : S₀ α) → rank₀ t̂ ≤ β → S₀ β
  liftS₀ (t , _) p = t , p

  liftS' : ∀ {α β} → (t̂ : S₀ α) → rank₀ t̂ ≤ β → S̃/ β
  liftS' {α} {β} t̂ p = S̃ β ⊢[ liftS₀ t̂ p ]

  liftS : ∀ {α β} → (t̂ : S₀ α) → rank (S̃ α ⊢[ t̂ ]) ≤ β → S̃/ β
  liftS {α} {β} t̂ p = liftS' t̂ p'
    where
    p' : rank₀ t̂ Z.≤ β
    p' = ≡.substp (_≤ β) (rank-beta t̂) p
    
  liftS-cong
    : ∀ {α β} → (ŝ t̂ : S₀ α)
    → (s≤β : rank (S̃ α ⊢[ ŝ ]) ≤ β)
    → (t≤β : rank (S̃ α ⊢[ t̂ ]) ≤ β)
    → (p : ŝ ≈ˢ t̂)
    → liftS ŝ s≤β ≡ liftS t̂ t≤β
  liftS-cong {α} {β} ŝ t̂ s≤β t≤β p = S̃ β ⊢≈[ p ]

  liftS/ : ∀ {α β} → (t̃ : S̃/ α) → rank t̃ ≤ β → S̃/ β
  liftS/ {α} {β} =
    SQ.elim (S̃ α) (λ t̃ → rank t̃ ≤ β → S̃/ β)
            (λ t̂ ρ≤β → liftS t̂ ρ≤β)
            (λ {ŝ t̂} p → dfunExtp {A = S̃/ α} {B = λ t̃ → rank t̃ ≤ β} (S̃ α ⊢≈[ p ])
               (λ ρs≤β → S̃ β ⊢≈[ p ]))

  liftS-beta : ∀ {α β} → (t̂ : S₀ α) → (ρt≤β : rank (S̃ α ⊢[ t̂ ]) ≤ β)
             → liftS/ (S̃ α ⊢[ t̂ ]) ρt≤β ≡ liftS t̂ ρt≤β 
  liftS-beta {α} {β} t̂ ρ≤β = funExtp⁻ (p t̂) ρ≤β
    where
    p : (t̂ : S₀ α) → liftS/ (S̃ α ⊢[ t̂ ]) ≡ liftS t̂
    p = SQ.elim-beta (S̃ α) (λ t̃ → rank t̃ ≤ β → S̃/ β)
            (λ t̂ ρ≤β → liftS t̂ ρ≤β)
            λ {ŝ t̂} p → dfunExtp {A = S̃/ α} {B = λ t̃ → rank t̃ ≤ β} (S̃ α ⊢≈[ p ])
               (λ ρs≤β → S̃ β ⊢≈[ p ])

  liftC₀ : ∀ {β} → (x : D*₀) → rankC (D* ⊢[ x ]) ≤ β → S̃/ β
  liftC₀ {β} x@(α , s̃) ρx≤β = liftS/ s̃ ρx≤β'
    where
    ρx≤β' : rank s̃ ≤ β
    ρx≤β' = substp (_≤ β) (rankC-beta x) ρx≤β

  liftC-cong : ∀ {β} {x y} → (p : D* [ x ≈ y ])
             → (ρx≤β : rankC (D* ⊢[ x ]) ≤ β)
             → (ρy≤β : rankC (D* ⊢[ y ]) ≤ β)
             → liftC₀ x ρx≤β ≡ liftC₀ y ρy≤β
  liftC-cong {β} (≈lstage i ≡.refl) ρx≤β ρy≤β = ≡.refl
  liftC-cong {β} {x@(α , s̃)} {y@(α' , t̃)} (≈lstep p s̃) =
    SQ.elimp (S̃ α)
      (λ s̃ → (ρx≤β : rankC (D* ⊢[ (α , s̃) ]) ≤ β)
           → (ρy≤β : rankC (D* ⊢[ (α' , dweaken/ p s̃) ]) ≤ β)
           → liftC₀ (α , s̃) ρx≤β ≡ liftC₀ (α' , dweaken/ p s̃) ρy≤β)
      q
      s̃
    where
    q : (ŝ : S₀ α)
      → (ρx≤β : rankC (D* ⊢[ (α , S̃ α ⊢[ ŝ ]) ]) ≤ β)
      → (ρy≤β : rankC (D* ⊢[ (α' , dweaken/ p (S̃ α ⊢[ ŝ ])) ]) ≤ β)
      → liftC₀ (α , S̃ α ⊢[ ŝ ]) ρx≤β
      ≡ liftC₀ (α' , dweaken/ p (S̃ α ⊢[ ŝ ])) ρy≤β
    q ŝ ρx≤β ρy≤β = 
      liftC₀ (α , (S̃ α ⊢[ ŝ ])) ρx≤β
        ≡⟨ ≡.refl ⟩
      liftS/ (S̃ α ⊢[ ŝ ]) (substp (_≤ β) (rankC-beta (α , (S̃ α ⊢[ ŝ ]))) ρx≤β)
        ≡⟨ liftS-beta ŝ ρs≤β ⟩
      liftS ŝ ρs≤β
        ≡⟨ ≡.refl ⟩
      liftS (dweaken₀ p ŝ) ρt≤βr
        ≡⟨ ≡.sym (liftS-beta (dweaken₀ p ŝ) ρt≤βr) ⟩
      liftS/ (S̃ α' ⊢[ dweaken₀ p ŝ ]) ρt≤βr
        ≡⟨ dcongsp liftS/ (≡.sym (dweaken-beta p ŝ)) ⟩
      liftS/ (dweaken/ p (S̃ α ⊢[ ŝ ]))
             (substp (_≤ β) (rankC-beta (α' , (dweaken/ p (S̃ α ⊢[ ŝ ])))) ρy≤β)
        ≡⟨ ≡.refl ⟩
      liftC₀ (α' , dweaken/ p (S̃ α ⊢[ ŝ ])) ρy≤β ∎
      where
      open ≡.≡-Reasoning
      ρs≤β : rank (S̃ α ⊢[ ŝ ]) ≤ β
      ρs≤β = substp (_≤ β) (rankC-beta (α , (S̃ α ⊢[ ŝ ]))) ρx≤β

      ρt≤βq : rank (dweaken/ p (S̃ α ⊢[ ŝ ])) ≤ β
      ρt≤βq = substp (_≤ β) (rankC-beta (α' , (dweaken/ p (S̃ α ⊢[ ŝ ])))) ρy≤β

      ρt≤βr : rank (S̃ α' ⊢[ dweaken₀ p ŝ ]) ≤ β
      ρt≤βr = substp (_≤ β) (≡.cong rank (dweaken-beta p ŝ)) ρt≤βq

  liftC-cong {β} {x@(αs , s̃)} {y@(αt , t̃)} (≈lsym p) ρx≤β ρy≤β =
    ≡.sym (liftC-cong p ρy≤β ρx≤β)
  liftC-cong {β} {x@(αs , s̃)} {y@(αt , t̃)} (≈ltrans {t = z} p p₁) ρx≤β ρy≤β =
    ≡.trans (liftC-cong p ρx≤β ρz≤β)
            (liftC-cong p₁ ρz≤β ρy≤β)
    where
    ρz≤β : rankC (D* ⊢[ z ]) ≤ β
    ρz≤β = substp (_≤ β) (rankC-dp p) ρx≤β

  liftC₀-dcong : ∀ {β β'} (r : β ≡ β') (x : D*₀) (ρ : rankC (D* ⊢[ x ]) ≤ β)
    → subst D̃/.ob r (liftC₀ x ρ)
    ≡ liftC₀ x (substp (rankC (D* ⊢[ x ]) ≤_) r ρ)
  liftC₀-dcong ≡.refl x ρ = ≡.refl

  liftC : D*/ → D*₀
  liftC =
    SQ.rec D*
      (λ x → rankC (D* ⊢[ x ]) , liftC₀ x (Z.≤refl (rankC (D* ⊢[ x ]))))
      (λ {x y} p → ≡.Σ≡ (rankC-dp p) (q (D* ⊢≈[ p ])))
    where
    q : ∀ {x y} → (p : (D* ⊢[ x ]) ≡ (D* ⊢[ y ]))
      → subst D̃/.ob (≡.cong rankC p) (liftC₀ x (Z.≤refl (rankC (D* ⊢[ x ]))))
      ≡ liftC₀ y (Z.≤refl (rankC (D* ⊢[ y ])))
    q {x} {y} p =
      subst D̃/.ob (≡.cong rankC p) (liftC₀ x (Z.≤refl (rankC (D* ⊢[ x ]))))
        ≡⟨ subst-irrel {B = D̃/.ob}
             (≡.cong rankC p)
             (rankC-dp r)
             (liftC₀ x (Z.≤refl (rankC (D* ⊢[ x ])))) ⟩
      subst D̃/.ob (rankC-dp r) (liftC₀ x (Z.≤refl (rankC (D* ⊢[ x ]))))
        ≡⟨ liftC₀-dcong (rankC-dp r) x (Z.≤refl (rankC (D* ⊢[ x ]))) ⟩
      liftC₀ x ρx≤y
        ≡⟨ liftC-cong r ρx≤y (Z.≤refl (rankC (D* ⊢[ y ]))) ⟩
      liftC₀ y (Z.≤refl (rankC (D* ⊢[ y ]))) ∎
      where
      open ≡.≡-Reasoning
      r : D* [ x ≈ y ]
      r = SQ.effectiveness D* x y p

      ρx≤y : rankC (D* ⊢[ x ]) ≤ rankC (D* ⊢[ y ])
      ρx≤y = substp (rankC (D* ⊢[ x ]) ≤_) (rankC-dp r)
                (Z.≤refl (rankC (D* ⊢[ x ])))

--   liftC-beta : (x : D*₀) → liftC (D* ⊢[ x ]) ≡ (rankC (D* ⊢[ x ]) , liftC₀ x)
--   liftC-beta =
--     SQ.rec-beta (D*)
--       (λ x → rankC (D* ⊢[ x ]) , liftC₀ x)
--       (λ p → ≡.Σ≡ (rankC-dp p) (liftC-cong p))

-- --   weakenLift : ∀ {α} (ŝ : S̃/ α) → dweaken/ (rank≤ ŝ) {!lift≈ ŝ!} ≡ ŝ
-- --   weakenLift {α} = SQ.elimp (S̃ α) B u
-- --     where
-- --     B : S̃/ α → Prop _
-- --     B ŝ = dweaken/ (rank≤ ŝ) {!lift≈ ŝ!} ≡ ŝ

-- --     u : ∀ a → B (S̃ α ⊢[ a ])
-- --     u a =
-- --       dweaken/ (rank≤ (S̃ α ⊢[ a ])) {!lift≈ (S̃ α ⊢[ a ])!}
-- --         ≡⟨ ≡.cong (dweaken/ (rank≤ (S̃ α ⊢[ a ]))) {!lift≈-beta a!} ⟩
-- --       dweaken/ (rank≤ (S̃ α ⊢[ a ]))
-- --         (subst S̃/ (≡.sym (rank-beta a)) {!lift/ a!})
-- --         ≡⟨ ≡.cong (dweaken/ (rank≤ (S̃ α ⊢[ a ])))
-- --                  (≡.sym (subst-quot-S (≡.sym (rank-beta a)) (lift₀ a))) ⟩
-- --       dweaken/ (rank≤ (S̃ α ⊢[ a ]))
-- --         (S̃ (rank (S̃ α ⊢[ a ])) ⊢[ subst S₀ (≡.sym (rank-beta a)) {!lift₀ a!} ])
-- --         ≡⟨ dweaken-beta (rank≤ (S̃ α ⊢[ a ]))
-- --                          (subst S₀ (≡.sym (rank-beta a)) (lift₀ a)) ⟩
-- --       S̃ α ⊢[ dweaken₀ (rank≤ (S̃ α ⊢[ a ]))
-- --                       (subst S₀ (≡.sym (rank-beta a)) {!lift₀ a!}) ]
-- --         ≡⟨ S̃ α ⊢≈[ ≡→≈ T̃ (subst-S₀-fst (≡.sym (rank-beta a)) {!lift₀ a!}) ] ⟩
-- --       S̃ α ⊢[ a ] ∎
-- --       where
-- --       open ≡.≡-Reasoning

-- --   dweaken-cast : ∀ {α β γ} (r : α ≡ β)
-- --     → (p : α ≤ γ) (q : β ≤ γ) (ŝ : S̃/ α)
-- --     → dweaken/ p ŝ ≡ dweaken/ q (subst S̃/ r ŝ)
-- --   dweaken-cast ≡.refl p q ŝ = ≡.refl

-- --   weakenLiftC : ∀ {α β} (p : α ≤ β) (ŝ : S̃/ α)
-- --     → dweaken/ (≤≤ p (rank≤ ŝ)) (subst S̃/ (rankC-beta (α , ŝ)) (liftC₀ (α , ŝ)))
-- --     ≡ dweaken/ p ŝ
-- --   weakenLiftC {α} {β} p ŝ =
-- --     dweaken/ (≤≤ p (rank≤ ŝ)) (subst S̃/ (rankC-beta (α , ŝ)) (liftC₀ (α , ŝ)))
-- --       ≡⟨ ≡.cong (dweaken/ (≤≤ p (rank≤ ŝ))) (subst-inv S̃/ (≡.sym (rankC-beta (α , ŝ)))) ⟩
-- --     dweaken/ (≤≤ p (rank≤ ŝ)) {!lift≈ ŝ!}
-- --       ≡⟨ comp (box (rank≤ ŝ)) (box p) {x = {!lift≈ ŝ!}} ⟩
-- --     dweaken/ p (dweaken/ (rank≤ ŝ) {!lift≈ ŝ!})
-- --       ≡⟨ ≡.cong (dweaken/ p) (weakenLift ŝ) ⟩
-- --     dweaken/ p ŝ ∎
-- --     where
-- --     open ≡.≡-Reasoning

-- --   isSectLiftC₀
-- --     : ∀ (x : D*₀)
-- --     → D* ⊢[ liftC (D* ⊢[ x ]) ]
-- --     ≡ D* ⊢[ x ]
-- --   isSectLiftC₀ x@(α , ŝ) = D* ⊢≈[ p ]
-- --     where
-- --     v : dweaken/ (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x)) ≡ ŝ
-- --     v = ≡.trans
-- --           (≡.cong (dweaken/ (rank≤ ŝ)) (subst-inv S̃/ (≡.sym (rankC-beta x))))
-- --           (weakenLift ŝ)
-- --     p : D* [ liftC (D* ⊢[ x ]) ≈ x ]
-- --     p =
-- --       liftC (D* ⊢[ x ])
-- --         ≈⟨ ≡→≈ (D*) (liftC-beta x) ⟩
-- --       rankC (D* ⊢[ x ]) , liftC₀ x
-- --         ≈⟨ ≡→≈ (D*) (Σ≡ (rankC-beta x) ≡.refl) ⟩
-- --       rankC₀ x , subst S̃/ (rankC-beta x) (liftC₀ x)
-- --         ≈⟨ ≈lstep (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x)) ⟩
-- --       α , dweaken/ (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x))
-- --         ≈⟨ ≈lstage α v ⟩
-- --       α , ŝ ∎
-- --       where
-- --       open ≈.≈syntax {S = D*}

-- --   isSectLiftC : ∀ (x : D*/) → D* ⊢[ liftC x ] ≡ x
-- --   isSectLiftC = SQ.elimp (D*) (λ z → D* ⊢[ liftC z ] ≡ z) isSectLiftC₀

-- -- module Cocontinuity where
-- --   open Rank
-- --   open LiftElement

-- --   ϕ₀ : FD*₀ → F.ob D*/
-- --   ϕ₀ (α , s , f) = s , λ i → D* ⊢[ α , f i ]
-- --   ϕ-cong : ∀ {x y : FD*₀} → Colim (FD̃/) [ x ≈ y ] → ϕ₀ x ≡ ϕ₀ y
-- --   ϕ-cong {α , a , f̂} {α , a , f̂} (≈lstage α ≡.refl) = ≡.refl
-- --   ϕ-cong {α , a , f̂} {β , a , ĝ} (≈lstep p (a , f̂)) =
-- --     ≡.cong (a ,_) (funExt (λ i → D* ⊢≈[ ≈lstep p (f̂ i) ]))
-- --   ϕ-cong {α , a , f̂} {β , b , ĝ} (≈lsym p) = ≡.sym (ϕ-cong p)
-- --   ϕ-cong {α , a , f̂} {β , b , ĝ} (≈ltrans p q) = ≡.trans (ϕ-cong p) (ϕ-cong q)

-- --   ϕ : Colim/ FD̃/ → F.ob D*/
-- --   ϕ = SQ.rec FD* ϕ₀ ϕ-cong

-- --   ϕ-beta : (x : FD*₀) → ϕ (Colim (FD̃/) ⊢[ x ]) ≡ ϕ₀ x
-- --   ϕ-beta = SQ.rec-beta (Colim (FD̃/)) ϕ₀ ϕ-cong

-- --   abstract
-- --     ϕ[] : FD*₀ → F.ob D*/
-- --     ϕ[] x = ϕ (Colim (FD̃/) ⊢[ x ])

-- --     ϕ[]-beta : (x : FD*₀) → ϕ[] x ≡ ϕ₀ x
-- --     ϕ[]-beta x = ϕ-beta x
-- --   {-# NOT_PROJECTION_LIKE ϕ[] #-}
-- --   {-# REWRITE ϕ[]-beta #-}

-- --   ψ : F.ob D*/ → FD*/
-- --   ψ (s , f̂) = FD* ⊢[ α , s , x̂ ]
-- --     where
-- --     μ : P s → Z
-- --     μ i = liftC (f̂ i) .proj₁
-- --     ĝ : ∀ i → S̃/ (μ i)
-- --     ĝ i = liftC (f̂ i) .proj₂
-- --     α : Z
-- --     α = Z.sup (s , μ)
-- --     x̂ : P s → S̃/ α
-- --     x̂ i = dweaken/ (child≤ s μ i) (ĝ i)

-- --   ϕψ : ∀ x → ϕ (ψ x) ≡ x
-- --   ϕψ x@(s , f̂) =
-- --     ϕ (FD* ⊢[ α , s , x̂ ])
-- --       ≡⟨ ϕ-beta (α , s , x̂) ⟩
-- --     s , (λ i → D* ⊢[ α , x̂ i ])
-- --       ≡⟨ ≡.cong (s ,_) (funExt (λ i → D* ⊢≈[ p i ])) ⟩
-- --     s , (λ i → D* ⊢[ liftC (f̂ i) ])
-- --       ≡⟨ ≡.cong (s ,_) (funExt (λ i → isSectLiftC (f̂ i))) ⟩
-- --     s , f̂ ∎
-- --     where
-- --     μ : P s → Z
-- --     μ i = liftC (f̂ i) .proj₁
-- --     ĝ : ∀ i → S̃/ (μ i)
-- --     ĝ i = liftC (f̂ i) .proj₂
-- --     α : Z
-- --     α = Z.sup (s , μ)
-- --     x̂ : P s → S̃/ α
-- --     x̂ i = dweaken/ (child≤ s μ i) (ĝ i)
-- --     p : ∀ i → D* [ (α , x̂ i) ≈ liftC (f̂ i) ]
-- --     p i = ≈lsym (≈lstep (child≤ s μ i) (ĝ i))
-- --     open ≡.≡-Reasoning

-- --   ψϕ : ∀ x → ψ (ϕ x) ≡ x
-- --   ψϕ x = SQ.elimp FD* (λ x → ψ (ϕ x) ≡ x) p x
-- --     where
-- --     open ≡.≡-Reasoning
-- --     p : ∀ (x : FD*₀) → ψ (ϕ (FD* ⊢[ x ])) ≡ FD* ⊢[ x ]
-- --     p (α , s , f̂) =
-- --       ψ (ϕ (FD* ⊢[ α , s , f̂ ]))
-- --         ≡⟨ ≡.cong ψ (ϕ-beta (α , s , f̂)) ⟩
-- --       ψ (s , λ i → D* ⊢[ α , f̂ i ])
-- --         ≡⟨ (FD* ⊢≈[ q ]) ⟩
-- --       (FD* ⊢[ α , s , f̂ ]) ∎
-- --       where
-- --       μ : P s → Z
-- --       μ i = liftC (D* ⊢[ α , f̂ i ]) .proj₁

-- --       β : Z
-- --       β = Z.sup (s , μ)

-- --       ĝ : ∀ i → S̃/ (μ i)
-- --       ĝ i = liftC (D* ⊢[ α , f̂ i ]) .proj₂

-- --       x̂ : P s → S̃/ β
-- --       x̂ i = dweaken/ (child≤ s μ i) (ĝ i)

-- --       γ : Z
-- --       γ = α ∨ᶻ β

-- --       h : ∀ i → dweaken/ (Z.<→≤ (Z.∨ᶻ-r< {α} {β})) (x̂ i)
-- --               ≡ dweaken/ (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (f̂ i)
-- --       h i =
-- --         ≡.trans
-- --           (≡.sym (comp (box (child≤ s μ i)) (box (Z.<→≤ (Z.∨ᶻ-r< {α} {β}))) {x = ĝ i}))
-- --           (≡.trans
-- --             (dweaken-cast r₁ p₁ q₁ (ĝ i))
-- --             (≡.trans
-- --               (≡.cong
-- --                 (dweaken/ q₁)
-- --                 (Σ-proj₂ (liftC-beta (α , f̂ i))))
-- --               (≡.trans
-- --                 (dweaken-cast r₂ q₁ q₂ (liftC₀ (α , f̂ i)))
-- --                 (weakenLiftC (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (f̂ i)))))
-- --         where
-- --         r₁ : μ i ≡ rankC (D* ⊢[ α , f̂ i ])
-- --         r₁ = ≡.cong proj₁ (liftC-beta (α , f̂ i))

-- --         p₁ : μ i ≤ γ
-- --         p₁ = ≤≤ (Z.<→≤ (Z.∨ᶻ-r< {α} {β})) (child≤ s μ i)

-- --         q₁ : rankC (D* ⊢[ α , f̂ i ]) ≤ γ
-- --         q₁ = ≡.substp (_≤ γ) r₁ p₁

-- --         r₂ : rankC (D* ⊢[ α , f̂ i ]) ≡ rank (f̂ i)
-- --         r₂ = rankC-beta (α , f̂ i)

-- --         q₂ : rank (f̂ i) ≤ γ
-- --         q₂ = ≡.substp (_≤ γ) r₂ q₁

-- --         p₂ : rank (f̂ i) ≤ γ
-- --         p₂ = ≤≤ (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (rank≤ (f̂ i))

-- --       q : FD* [ (β , s , x̂) ≈ (α , s , f̂) ]
-- --       q = ≈ltrans
-- --             (≈lstep (Z.<→≤ (Z.∨ᶻ-r< {α} {β})) (s , x̂))
-- --             (≈ltrans
-- --               (≈lstage γ (≡.cong (s ,_) (funExt h)))
-- --               (≈lsym (≈lstep (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (s , f̂))))
