open import QIT.Prelude hiding (ℓD; lift)
open import QIT.Prop
open import QIT.Types
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Relation.SetQuotient
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Set.Bijection
open import QIT.QW.Signature
open import QIT.QW.Subclasses using (DepthPreservingSig)
open import QIT.QW.Plump

module QIT.QW.Cocontinuity.FromDepthPreservation
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
  where

private
  ℓD = ℓA ⊔ ℓS ⊔ ℓP
  ℓD' = ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV

open Sig sig
open FunExt funExt*
open ExtensionalPlumpOrdinals extensionalPlumpOrdinals*
open DepthPreservingSig depthPreserving*

open import QIT.QW.Stage sig Zᴬ
open import QIT.QW.Diagram sig Zᴬ
open import QIT.Plump.Properties Zᴬ as Z

open import QIT.Container.Base
open import QIT.Functor.Properties
open import QIT.Container.StrictFunctor S P (ℓD ⊔ ℓD')
open import QIT.Category.Morphism (SetCat (ℓD ⊔ ℓD'))
open import QIT.Setoid.Quotient
open import QIT.QW.Equation
open import QIT.Colimit.Base ≤p ℓD ℓD'
open import QIT.Container.Properties

dpᵗ : ∀ s t → s ≈ᵗ t → ιᶻ s ≡ ιᶻ t
dpᵗ s t (≈tcong a f g r) =
  ≡.cong (λ ○ → Z.sup (a , ○))
          (funExt (λ i → dpᵗ (f i) (g i) (r i)))
dpᵗ s t (≈tsat e ϕ) = 
  let ∧i p , q = ιᶻ≤≥ιᶻ (lhs' e ϕ) (rhs' e ϕ)
                        (dpe e λ v → lower (ϕ v))
  in antisym p q
dpᵗ s t ≈trefl = ≡.refl
dpᵗ s t (≈tsym p) = ≡.sym (dpᵗ t s p)
dpᵗ s t (≈ttrans p q) = ≡.trans (dpᵗ s _ p) (dpᵗ _ t q)

dp : ∀ {α β} (ŝ : S₀ α) (t̂ : S₀ β) → ŝ ≈ˢ t̂ → ιᶻ (ŝ .fst) ≡ ιᶻ (t̂ .fst)
dp (s , _) (t , _) p = dpᵗ s t p

module Rank where
  rank₀ : ∀ {α} → S₀ α → Z
  rank₀ (t , _) = ιᶻ t

  rank-cong : ∀ {α β} (ŝ  : S₀ α) (t̂ : S₀ β) → ŝ ≈ˢ t̂ → rank₀ ŝ ≡ rank₀ t̂
  rank-cong ŝ t̂ p = dp ŝ t̂ p

  rank : ∀ {α} → S̃/ α → Z
  rank {α} = SQ.rec (S̃ α) rank₀ λ {ŝ t̂} → rank-cong ŝ t̂

  rank-beta : ∀ {α} (t̂ : S₀ α) → rank (S̃ α ⊢[ t̂ ]) ≡ rank₀ t̂
  rank-beta {α} t̂ = SQ.rec-beta (S̃ α) rank₀ (λ {ŝ t̂} → rank-cong ŝ t̂) t̂

  rank₀≤ : ∀ {α} → (ŝ : S₀ α) → rank₀ ŝ ≤ α
  rank₀≤ {α} (s , s≤α) = s≤α

  rank≤ : ∀ {α} → (ŝ : S̃/ α) → rank ŝ ≤ α
  rank≤ {α} = SQ.elimp (S̃ α) (λ ŝ → rank ŝ ≤ α) p
    where
    p : ∀ ŝ → rank (S̃ α ⊢[ ŝ ]) ≤ α
    p ŝ = ≡.substp (_≤ α) (≡.sym (rank-beta ŝ)) (rank₀≤ ŝ)

  rankC₀ : Colim₀ D̃/ → Z
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

  rankC-cong : ∀ {x y} → Colim D̃/ [ x ≈ y ]
             → rankC₀ x ≡ rankC₀ y
  rankC-cong (≈lstage i p) = ≡.cong rank p
  rankC-cong (≈lstep p x) = rank-step p x
  rankC-cong (≈lsym p) =
    ≡.sym (rankC-cong p)
  rankC-cong (≈ltrans p q) =
    ≡.trans (rankC-cong p) (rankC-cong q)

  rankC : Colim/ D̃/ → Z
  rankC = SQ.rec (Colim D̃/) rankC₀ rankC-cong

  rankC-beta : (x : Colim₀ D̃/) → rankC (Colim D̃/ ⊢[ x ]) ≡ rankC₀ x
  rankC-beta = SQ.rec-beta (Colim D̃/) rankC₀ rankC-cong

  rankC-dp : ∀ {x y} → Colim D̃/ [ x ≈ y ]
           → rankC (Colim D̃/ ⊢[ x ]) ≡ rankC (Colim D̃/ ⊢[ y ])
  rankC-dp {x} {y} p =
    rankC (Colim D̃/ ⊢[ x ])
      ≡⟨ rankC-beta x ⟩
    rankC₀ x
      ≡⟨ rankC-cong p ⟩
    rankC₀ y
      ≡⟨ ≡.sym (rankC-beta y) ⟩
    rankC (Colim D̃/ ⊢[ y ]) ∎
    where
    open ≡.≡-Reasoning

module LiftElement where
  open SQ
  open Rank

  lift₀ : ∀ {α} → (t̂ : S₀ α) → S₀ (rank₀ t̂)
  lift₀ (t , _) = t , ≤refl (ιᶻ t)

  lift/ : ∀ {α} → (t̂ : S₀ α) → S̃ (rank₀ t̂) /≈
  lift/ {α} (t , t≤α) = S̃ (ιᶻ t) ⊢[ lift₀ (t , t≤α) ]

  lift-cong : ∀ {γ} {ŝ t̂ : S₀ γ} (p : S̃ γ [ ŝ ≈ t̂ ])
    → subst S̃/ (rank-cong ŝ t̂ p) (lift/ ŝ) ≡ lift/ t̂
  lift-cong {γ} {ŝ@(s , s≤γ)} {t̂@(t , t≤γ)} p =
    subst S̃/ r (lift/ ŝ)
      ≡⟨ ≡.cong (subst S̃/ r) (S̃ (ιᶻ s) ⊢≈[ q ]) ⟩
    subst S̃/ r (S̃ (ιᶻ s) ⊢[ subst S₀ r⁻ (lift₀ t̂) ]) 
      ≡⟨ ≡.cong (subst S̃/ r) (subst-quot-S r⁻ _) ⟩
    subst S̃/ r (subst S̃/ r⁻ (lift/ t̂))
      ≡⟨ subst-inv S̃/ r⁻ ⟩
    lift/ t̂ ∎
      where
      open ≡.≡-Reasoning
      r = dpᵗ s t p
      r⁻ = ≡.sym r
      q : s ≈ᵗ ⟨ subst S₀ r⁻ (lift₀ t̂) ⟩ᴾ
      q = ≈ttrans p (≡→≈ T̃ (≡.sym (subst-S₀-fst r⁻ (lift₀ t̂)) )) 

  lift≈₀ : ∀ {α} → (ŝ : S₀ α) → S̃/ (rank ([ S̃ α ] ŝ))
  lift≈₀ ŝ = subst S̃/ (≡.sym (rank-beta ŝ)) (lift/ ŝ)

  lift≈-cong : ∀ {α} {ŝ t̂ : S₀ α} (r : ŝ ≈ˢ t̂)
    → ≡.subst (λ t̂ → S̃/ (rank t̂)) (S̃ α ⊢≈[ r ]) (lift≈₀ ŝ)
    ≡ lift≈₀ t̂
  lift≈-cong {α} {ŝ} {t̂} r =
    subst (λ t̂ → S̃/ (rank t̂)) (S̃ α ⊢≈[ r ])
          (subst S̃/ (≡.sym (rank-beta ŝ)) (lift/ ŝ))
      ≡⟨ ≡.subst-cong S̃/ rank (S̃ α ⊢≈[ r ]) (subst S̃/ _ (lift/ ŝ)) ⟩
    subst S̃/ (≡.cong rank (S̃ α ⊢≈[ r ]))
          (subst S̃/ (≡.sym (rank-beta ŝ)) (lift/ ŝ))
      ≡⟨ ≡.subst-subst S̃/ (≡.sym (rank-beta ŝ))
                       (≡.cong rank (S̃ α ⊢≈[ r ])) (lift/ ŝ) ⟩
    subst S̃/ (≡.trans (≡.sym (rank-beta ŝ))
                       (≡.cong rank (S̃ α ⊢≈[ r ])))
              (lift/ ŝ)
      ≡⟨ subst-irrel _ _ (lift/ ŝ) ⟩
    subst S̃/ (≡.trans (rank-cong ŝ t̂ r)
                       (≡.sym (rank-beta t̂)))
              (lift/ ŝ)
      ≡⟨ ≡.sym (≡.subst-subst S̃/ (rank-cong ŝ t̂ r)
                       (≡.sym (rank-beta t̂)) (lift/ ŝ)) ⟩
    subst S̃/ (≡.sym (rank-beta t̂))
          (subst S̃/ (rank-cong ŝ t̂ r) (lift/ ŝ))
      ≡⟨ ≡.cong (subst S̃/ (≡.sym (rank-beta t̂)))
               (lift-cong {ŝ = ŝ} {t̂ = t̂} r) ⟩
    subst S̃/ (≡.sym (rank-beta t̂)) (lift/ t̂) ∎
    where
    open ≡.≡-Reasoning

  lift≈ : ∀ {α} → (t̂ : S̃/ α) → S̃/ (rank t̂)
  lift≈ {α} = SQ.elim (S̃ α) (λ t̂ → S̃/ (rank t̂)) lift≈₀ lift≈-cong

  lift≈-beta : ∀ {α} (ŝ : S₀ α) → lift≈ (S̃ α ⊢[ ŝ ]) ≡ lift≈₀ ŝ
  lift≈-beta {α} ŝ =
    SQ.elim-beta (S̃ α) (λ t̂ → S̃/ (rank t̂)) lift≈₀ lift≈-cong ŝ

  lift≈-step : ∀ {α β} (p : α ≤ β) (s̃ : S̃/ α)
    → (q : rank s̃ ≡ rank (D̃/.hom (box p) s̃))
    → subst S̃/ q (lift≈ s̃) ≡ lift≈ (D̃/.hom (box p) s̃)
  lift≈-step {α} {β} p =
    SQ.elimp (S̃ α) _ r
    where
    r : (a : S₀ α)
      → (q : rank (S̃ α ⊢[ a ]) ≡ rank (D̃/.hom (box p) (S̃ α ⊢[ a ])))
      → subst S̃/ q (lift≈ (S̃ α ⊢[ a ]))
      ≡ lift≈ (D̃/.hom (box p) (S̃ α ⊢[ a ]))
    r a q =
      subst S̃/ q (lift≈ (S̃ α ⊢[ a ]))
        ≡⟨ ≡.cong (subst S̃/ q) (lift≈-beta a) ⟩
      subst S̃/ q (subst S̃/ (≡.sym (rank-beta a)) (lift/ a))
        ≡⟨ ≡.subst-subst S̃/ (≡.sym (rank-beta a)) q (lift/ a) ⟩
      subst S̃/ (≡.trans (≡.sym (rank-beta a)) q) (lift/ a)
        ≡⟨ subst-irrel _ _ (lift/ a) ⟩
      subst S̃/
        (≡.trans (≡.sym (rank-beta (dweaken₀ p a)))
                  (≡.cong rank (≡.sym (dweaken-beta p a))))
        (lift/ a)
        ≡⟨ ≡.sym (≡.subst-subst S̃/
                     (≡.sym (rank-beta (dweaken₀ p a)))
                     (≡.cong rank (≡.sym (dweaken-beta p a)))
                     (lift/ a)) ⟩
      subst S̃/ (≡.cong rank (≡.sym (dweaken-beta p a)))
        (subst S̃/ (≡.sym (rank-beta (dweaken₀ p a))) (lift/ a))
        ≡⟨ ≡.cong (subst S̃/ (≡.cong rank (≡.sym (dweaken-beta p a))))
                 (≡.sym (lift≈-beta (dweaken₀ p a))) ⟩
      subst S̃/ (≡.cong rank (≡.sym (dweaken-beta p a)))
        (lift≈ (S̃ β ⊢[ dweaken₀ p a ]))
        ≡⟨ dcong-lift≈ (≡.sym (dweaken-beta p a)) ⟩
      lift≈ (D̃/.hom (box p) (S̃ α ⊢[ a ])) ∎
      where
      open ≡.≡-Reasoning

      dcong-lift≈ : ∀ {s̃ t̃ : S̃/ β} (e : s̃ ≡ t̃)
        → subst S̃/ (≡.cong rank e) (lift≈ s̃) ≡ lift≈ t̃
      dcong-lift≈ ≡.refl = subst-refl _

  liftC₀ : (x : Colim₀ D̃/) → S̃/ (rankC (Colim D̃/ ⊢[ x ]))
  liftC₀ x@(α , ŝ) = ≡.subst S̃/ p (lift≈ ŝ)
    where
    p : rank ŝ ≡ rankC (Colim D̃/ ⊢[ x ])
    p = ≡.sym (rankC-beta x)

  liftC-cong : ∀ {x y} → (p : Colim D̃/ [ x ≈ y ])
             → subst S̃/ (rankC-dp p) (liftC₀ x) ≡ liftC₀ y
  liftC-cong {(α , s̃)} {(α , t̃)} (≈lstage α e) =
    subst S̃/ (rankC-dp (≈lstage α e)) (liftC₀ (α , s̃))
      ≡⟨ subst-irrel _ _ (liftC₀ (α , s̃)) ⟩
    subst S̃/ (≡.cong (λ z → rankC (Colim D̃/ ⊢[ z ])) (≡.cong (α ,_) e))
          (liftC₀ (α , s̃))
      ≡⟨ dcong-liftC₀ (≡.cong (α ,_) e) ⟩
    liftC₀ (α , t̃) ∎
    where
    open ≡.≡-Reasoning

    dcong-liftC₀ : ∀ {x y} (e : x ≡ y)
      → subst S̃/ (≡.cong (λ z → rankC (Colim D̃/ ⊢[ z ])) e) (liftC₀ x)
      ≡ liftC₀ y
    dcong-liftC₀ ≡.refl = subst-refl _
  liftC-cong {(α , s̃)} {(β , t̃)} (≈lstep p s̃) =
    subst S̃/ (rankC-dp (≈lstep p s̃)) (liftC₀ (α , s̃))
      ≡⟨ ≡.subst-subst S̃/ (≡.sym (rankC-beta (α , s̃)))
                           (rankC-dp (≈lstep p s̃)) (lift≈ s̃) ⟩
    subst S̃/ (≡.trans (≡.sym (rankC-beta (α , s̃)))
                       (rankC-dp (≈lstep p s̃)))
          (lift≈ s̃)
      ≡⟨ subst-irrel _ _ (lift≈ s̃) ⟩
    subst S̃/ (≡.trans (rankC-cong (≈lstep p s̃))
                       (≡.sym (rankC-beta (β , D̃/.hom (box p) s̃))))
          (lift≈ s̃)
      ≡⟨ ≡.sym (≡.subst-subst S̃/ (rankC-cong (≈lstep p s̃))
                           (≡.sym (rankC-beta (β , D̃/.hom (box p) s̃)))
                           (lift≈ s̃)) ⟩
    subst S̃/ (≡.sym (rankC-beta (β , D̃/.hom (box p) s̃)))
          (subst S̃/ (rankC-cong (≈lstep p s̃)) (lift≈ s̃))
      ≡⟨ ≡.cong (subst S̃/ (≡.sym (rankC-beta (β , D̃/.hom (box p) s̃))))
               (lift≈-step p s̃ (rankC-cong (≈lstep p s̃))) ⟩
    liftC₀ (β , D̃/.hom (box p) s̃) ∎
    where
    open ≡.≡-Reasoning
  liftC-cong {x} {y} (≈lsym p) =
    subst S̃/ (rankC-dp (≈lsym p)) (liftC₀ x)
      ≡⟨ subst-irrel _ _ (liftC₀ x) ⟩
    subst S̃/ (≡.sym (rankC-dp p)) (liftC₀ x)
      ≡⟨ ≡.dsym S̃/ (rankC-dp p) (liftC-cong p) ⟩
    liftC₀ y ∎
    where
    open ≡.≡-Reasoning
  liftC-cong {x} {z} (≈ltrans {t = y} p q) =
    subst S̃/ (rankC-dp (≈ltrans p q)) (liftC₀ x)
      ≡⟨ subst-irrel _ _ (liftC₀ x) ⟩
    subst S̃/ (≡.trans (rankC-dp p) (rankC-dp q)) (liftC₀ x)
      ≡⟨ ≡.sym (≡.subst-subst S̃/ (rankC-dp p) (rankC-dp q) (liftC₀ x)) ⟩
    subst S̃/ (rankC-dp q) (subst S̃/ (rankC-dp p) (liftC₀ x))
      ≡⟨ ≡.cong (subst S̃/ (rankC-dp q)) (liftC-cong p) ⟩
    subst S̃/ (rankC-dp q) (liftC₀ y)
      ≡⟨ liftC-cong q ⟩
    liftC₀ z ∎
    where
    open ≡.≡-Reasoning

  liftC : Colim/ D̃/ → Colim₀ D̃/
  liftC =
    SQ.rec (Colim D̃/)
      (λ x → rankC (Colim D̃/ ⊢[ x ]) , liftC₀ x)
      (λ p → ≡.Σ≡ (rankC-dp p) (liftC-cong p))

  liftC-beta : (x : Colim₀ D̃/) → liftC (_ ⊢[ x ]) ≡ (rankC (Colim D̃/ ⊢[ x ]) , liftC₀ x)
  liftC-beta =
    SQ.rec-beta (Colim D̃/)
      (λ x → rankC (Colim D̃/ ⊢[ x ]) , liftC₀ x)
      (λ p → ≡.Σ≡ (rankC-dp p) (liftC-cong p))

  weakenLift : ∀ {α} (ŝ : S̃/ α) → dweaken/ (rank≤ ŝ) (lift≈ ŝ) ≡ ŝ
  weakenLift {α} = SQ.elimp (S̃ α) B u
    where
    B : S̃/ α → Prop _
    B ŝ = dweaken/ (rank≤ ŝ) (lift≈ ŝ) ≡ ŝ

    u : ∀ a → B (S̃ α ⊢[ a ])
    u a =
      dweaken/ (rank≤ (S̃ α ⊢[ a ])) (lift≈ (S̃ α ⊢[ a ]))
        ≡⟨ ≡.cong (dweaken/ (rank≤ (S̃ α ⊢[ a ]))) (lift≈-beta a) ⟩
      dweaken/ (rank≤ (S̃ α ⊢[ a ]))
        (subst S̃/ (≡.sym (rank-beta a)) (lift/ a))
        ≡⟨ ≡.cong (dweaken/ (rank≤ (S̃ α ⊢[ a ])))
                 (≡.sym (subst-quot-S (≡.sym (rank-beta a)) (lift₀ a))) ⟩
      dweaken/ (rank≤ (S̃ α ⊢[ a ]))
        (S̃ (rank (S̃ α ⊢[ a ])) ⊢[ subst S₀ (≡.sym (rank-beta a)) (lift₀ a) ])
        ≡⟨ dweaken-beta (rank≤ (S̃ α ⊢[ a ]))
                         (subst S₀ (≡.sym (rank-beta a)) (lift₀ a)) ⟩
      S̃ α ⊢[ dweaken₀ (rank≤ (S̃ α ⊢[ a ]))
                      (subst S₀ (≡.sym (rank-beta a)) (lift₀ a)) ]
        ≡⟨ S̃ α ⊢≈[ ≡→≈ T̃ (subst-S₀-fst (≡.sym (rank-beta a)) (lift₀ a)) ] ⟩
      S̃ α ⊢[ a ] ∎
      where
      open ≡.≡-Reasoning

  isSectLiftC₀
    : ∀ (x : Colim₀ D̃/)
    → Colim D̃/ ⊢[ liftC (Colim D̃/ ⊢[ x ]) ]
    ≡ Colim D̃/ ⊢[ x ]
  isSectLiftC₀ x@(α , ŝ) = Colim D̃/ ⊢≈[ p ]
    where
    v : dweaken/ (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x)) ≡ ŝ
    v = ≡.trans
          (≡.cong (dweaken/ (rank≤ ŝ)) (subst-inv S̃/ (≡.sym (rankC-beta x))))
          (weakenLift ŝ)
    p : Colim D̃/ [ liftC (Colim D̃/ ⊢[ x ]) ≈ x ]
    p =
      liftC (Colim D̃/ ⊢[ x ])
        ≈⟨ ≡→≈ (Colim D̃/) (liftC-beta x) ⟩
      rankC (_ ⊢[ x ]) , liftC₀ x
        ≈⟨ ≡→≈ (Colim D̃/) (Σ≡ (rankC-beta x) ≡.refl) ⟩
      rankC₀ x , subst S̃/ (rankC-beta x) (liftC₀ x)
        ≈⟨ ≈lstep (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x)) ⟩
      α , dweaken/ (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x))
        ≈⟨ ≈lstage α v ⟩
      α , ŝ ∎
      where
      open ≈.≈syntax {S = Colim D̃/}

  isSectLiftC : ∀ (x : Colim/ D̃/) → Colim D̃/ ⊢[ liftC x ] ≡ x
  isSectLiftC = SQ.elimp (Colim D̃/) (λ z → Colim D̃/ ⊢[ liftC z ] ≡ z) isSectLiftC₀

module Cocontinuity where
  open Rank
  open LiftElement

  ϕ₀ : Colim₀ (F ∘ꟳ D̃/) → F.ob (Colim/ D̃/)
  ϕ₀ (α , s , f) = s , λ i → Colim D̃/ ⊢[ α , f i ]
  ϕ-cong : ∀ {x y : Colim₀ (F ∘ꟳ D̃/)} → Colim (F ∘ꟳ D̃/) [ x ≈ y ] → ϕ₀ x ≡ ϕ₀ y
  ϕ-cong {α , a , f̂} {α , a , f̂} (≈lstage α ≡.refl) = ≡.refl
  ϕ-cong {α , a , f̂} {β , a , ĝ} (≈lstep p (a , f̂)) =
    ≡.cong (a ,_) (funExt (λ i → Colim D̃/ ⊢≈[ ≈lstep p (f̂ i) ]))
  ϕ-cong {α , a , f̂} {β , b , ĝ} (≈lsym p) = ≡.sym (ϕ-cong p)
  ϕ-cong {α , a , f̂} {β , b , ĝ} (≈ltrans p q) = ≡.trans (ϕ-cong p) (ϕ-cong q)

  ϕ : Colim/ (F ∘ꟳ D̃/) → F.ob (Colim/ D̃/)
  ϕ = SQ.rec (Colim (F ∘ꟳ D̃/)) ϕ₀ ϕ-cong

  ψ : F.ob (Colim/ D̃/) → Colim/ (F ∘ꟳ D̃/)
  ψ (s , f̂) = Colim _ ⊢[ α , s , x̂ ]
    where
    μ : P s → Z
    μ i = liftC (f̂ i) .proj₁
    ĝ : ∀ i → S̃/ (μ i)
    ĝ i = liftC (f̂ i) .proj₂
    α : Z
    α = Z.sup (s , μ)
    x̂ : P s → S̃/ α
    x̂ i = dweaken/ (child≤ s μ i) (ĝ i)
