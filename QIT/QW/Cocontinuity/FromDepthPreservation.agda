open import QIT.Prelude hiding (ℓD; lift)
open import QIT.Prop
open import QIT.Types
open import QIT.Setoid
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Set
open import QIT.Container.Base
open import QIT.Function.Base
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
open import QIT.Setoid.Quotient

module QIT.QW.Cocontinuity.FromDepthPreservation
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

  rank-cong : ∀ {α β} (ŝ  : S₀ α) (t̂ : S₀ β) → ŝ ≈ˢ t̂ → rank₀ ŝ ≡ rank₀ t̂
  rank-cong ŝ t̂ p = dp ŝ t̂ p

  abstract
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
    p ŝ rewrite rank-beta ŝ =
      rank₀≤ ŝ

  rankC₀ : D*₀ → Z
  rankC₀ (_ , t̂) = rank t̂

  rank-step₀ : ∀ {α β} (p : α ≤ β) (t̂ : S₀ α)
            → rank (S̃ α ⊢[ t̂ ]) ≡ rank (D̃/.hom (box p) (S̃ α ⊢[ t̂ ]))
  rank-step₀ p t̂ rewrite
      rank-beta t̂
    | ≡.sym (rank-beta (dweaken₀ p t̂))
    | dweaken-beta p t̂ =
      ≡.refl

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

  abstract
    rankC : D*/ → Z
    rankC = SQ.rec D* rankC₀ rankC-cong

    rankC-beta : (x : D*₀) → rankC (D* ⊢[ x ]) ≡ rankC₀ x
    rankC-beta = SQ.rec-beta (D*) rankC₀ rankC-cong

  rankC-dp : ∀ {x y} → D* [ x ≈ y ]
           → rankC (D* ⊢[ x ]) ≡ rankC (D* ⊢[ y ])
  rankC-dp {x} {y} p
    rewrite rankC-beta x
          | rankC-beta y =
    rankC-cong p
    where
    open ≡.≡-Reasoning

module LiftElement where
  open DepthPreserving
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
      ≡⟨ subst-irrel
           (≡.trans (≡.sym (rank-beta ŝ))
                    (≡.cong rank (S̃ α ⊢≈[ r ])))
           (≡.trans (rank-cong ŝ t̂ r)
                    (≡.sym (rank-beta t̂)))
           (lift/ ŝ) ⟩
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
        ≡⟨ subst-irrel
             (≡.trans (≡.sym (rank-beta a)) q)
             (≡.trans (≡.sym (rank-beta (dweaken₀ p a)))
                      (≡.cong rank (≡.sym (dweaken-beta p a))))
             (lift/ a) ⟩
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
      dcong-lift≈ ≡.refl = ≡.refl

  liftC₀ : (x : D*₀) → S̃/ (rankC (D* ⊢[ x ]))
  liftC₀ x@(α , ŝ) = ≡.subst S̃/ p (lift≈ ŝ)
    where
    p : rank ŝ ≡ rankC (D* ⊢[ x ])
    p = ≡.sym (rankC-beta x)

  liftC-cong : ∀ {x y} → (p : D* [ x ≈ y ])
             → subst S̃/ (rankC-dp p) (liftC₀ x) ≡ liftC₀ y
  liftC-cong {(α , s̃)} {(α , t̃)} (≈lstage α e) =
    subst S̃/ (rankC-dp (≈lstage α e))
          (liftC₀ (α , s̃))
      ≡⟨ subst-irrel
           (rankC-dp (≈lstage α e))
           (≡.cong (λ z → rankC (D* ⊢[ z ])) (≡.cong (α ,_) e))
           (liftC₀ (α , s̃)) ⟩
    subst S̃/ (≡.cong (λ z → rankC (D* ⊢[ z ])) (≡.cong (α ,_) e))
          (liftC₀ (α , s̃))
      ≡⟨ dcong-liftC₀ (≡.cong (α ,_) e) ⟩
    liftC₀ (α , t̃) ∎
    where
    open ≡.≡-Reasoning

    dcong-liftC₀ : ∀ {x y} (e : x ≡ y)
      → subst S̃/ (≡.cong (λ z → rankC (D* ⊢[ z ])) e) (liftC₀ x)
      ≡ liftC₀ y
    dcong-liftC₀ ≡.refl = ≡.refl
  liftC-cong {(α , s̃)} {(β , t̃)} (≈lstep p s̃) =
    subst S̃/ (rankC-dp (≈lstep p s̃)) (liftC₀ (α , s̃))
      ≡⟨ ≡.subst-subst S̃/ (≡.sym (rankC-beta (α , s̃)))
                           (rankC-dp (≈lstep p s̃)) (lift≈ s̃) ⟩
    subst S̃/ (≡.trans (≡.sym (rankC-beta (α , s̃)))
                       (rankC-dp (≈lstep p s̃)))
          (lift≈ s̃)
      ≡⟨ subst-irrel
           (≡.trans (≡.sym (rankC-beta (α , s̃)))
                    (rankC-dp (≈lstep p s̃)))
           (≡.trans (rankC-cong (≈lstep p s̃))
                    (≡.sym (rankC-beta (β , D̃/.hom (box p) s̃))))
           (lift≈ s̃) ⟩
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
      ≡⟨ subst-irrel (rankC-dp (≈lsym p)) (≡.sym (rankC-dp p)) (liftC₀ x) ⟩
    subst S̃/ (≡.sym (rankC-dp p)) (liftC₀ x)
      ≡⟨ ≡.dsym S̃/ (rankC-dp p) (liftC-cong p) ⟩
    liftC₀ y ∎
    where
    open ≡.≡-Reasoning
  liftC-cong {x} {z} (≈ltrans {t = y} p q) =
    subst S̃/ (rankC-dp (≈ltrans p q)) (liftC₀ x)
      ≡⟨ subst-irrel
           (rankC-dp (≈ltrans p q))
           (≡.trans (rankC-dp p) (rankC-dp q))
           (liftC₀ x) ⟩
    subst S̃/ (≡.trans (rankC-dp p) (rankC-dp q)) (liftC₀ x)
      ≡⟨ ≡.sym (≡.subst-subst S̃/ (rankC-dp p) (rankC-dp q) (liftC₀ x)) ⟩
    subst S̃/ (rankC-dp q) (subst S̃/ (rankC-dp p) (liftC₀ x))
      ≡⟨ ≡.cong (subst S̃/ (rankC-dp q)) (liftC-cong p) ⟩
    subst S̃/ (rankC-dp q) (liftC₀ y)
      ≡⟨ liftC-cong q ⟩
    liftC₀ z ∎
    where
    open ≡.≡-Reasoning

  liftC : D*/ → D*₀
  liftC =
    SQ.rec (D*)
      (λ x → rankC (D* ⊢[ x ]) , liftC₀ x)
      (λ p → ≡.Σ≡ (rankC-dp p) (liftC-cong p))

  liftC-beta : (x : D*₀) → liftC (D* ⊢[ x ]) ≡ (rankC (D* ⊢[ x ]) , liftC₀ x)
  liftC-beta =
    SQ.rec-beta (D*)
      (λ x → rankC (D* ⊢[ x ]) , liftC₀ x)
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

  weaken-irrel : ∀ {α β} (p q : α ≤ β) (ŝ : S̃/ α) → dweaken/ p ŝ ≡ dweaken/ q ŝ
  weaken-irrel {α} {β} p q = SQ.elimp (S̃ α) B u
    where
    B : S̃/ α → Prop _
    B ŝ = dweaken/ p ŝ ≡ dweaken/ q ŝ

    u : ∀ a → B (S̃ α ⊢[ a ])
    u a =
      dweaken/ p (S̃ α ⊢[ a ])
        ≡⟨ dweaken-beta p a ⟩
      S̃ β ⊢[ dweaken₀ p a ]
        ≡⟨ S̃ β ⊢≈[ ≈trefl ] ⟩
      S̃ β ⊢[ dweaken₀ q a ]
        ≡⟨ ≡.sym (dweaken-beta q a) ⟩
      dweaken/ q (S̃ α ⊢[ a ]) ∎
      where
      open ≡.≡-Reasoning

  dweaken-cast : ∀ {α β γ} (r : α ≡ β)
    → (p : α ≤ γ) (q : β ≤ γ) (ŝ : S̃/ α)
    → dweaken/ p ŝ ≡ dweaken/ q (subst S̃/ r ŝ)
  dweaken-cast ≡.refl p q ŝ = weaken-irrel p q ŝ

  weakenLiftC : ∀ {α β} (p : α ≤ β) (ŝ : S̃/ α)
    → dweaken/ (≤≤ p (rank≤ ŝ)) (subst S̃/ (rankC-beta (α , ŝ)) (liftC₀ (α , ŝ)))
    ≡ dweaken/ p ŝ
  weakenLiftC {α} {β} p ŝ =
    dweaken/ (≤≤ p (rank≤ ŝ)) (subst S̃/ (rankC-beta (α , ŝ)) (liftC₀ (α , ŝ)))
      ≡⟨ ≡.cong (dweaken/ (≤≤ p (rank≤ ŝ))) (subst-inv S̃/ (≡.sym (rankC-beta (α , ŝ)))) ⟩
    dweaken/ (≤≤ p (rank≤ ŝ)) (lift≈ ŝ)
      ≡⟨ comp (box (rank≤ ŝ)) (box p) {x = lift≈ ŝ} ⟩
    dweaken/ p (dweaken/ (rank≤ ŝ) (lift≈ ŝ))
      ≡⟨ ≡.cong (dweaken/ p) (weakenLift ŝ) ⟩
    dweaken/ p ŝ ∎
    where
    open ≡.≡-Reasoning

  isSectLiftC₀
    : ∀ (x : D*₀)
    → D* ⊢[ liftC (D* ⊢[ x ]) ]
    ≡ D* ⊢[ x ]
  isSectLiftC₀ x@(α , ŝ) = D* ⊢≈[ p ]
    where
    v : dweaken/ (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x)) ≡ ŝ
    v = ≡.trans
          (≡.cong (dweaken/ (rank≤ ŝ)) (subst-inv S̃/ (≡.sym (rankC-beta x))))
          (weakenLift ŝ)
    p : D* [ liftC (D* ⊢[ x ]) ≈ x ]
    p =
      liftC (D* ⊢[ x ])
        ≈⟨ ≡→≈ (D*) (liftC-beta x) ⟩
      rankC (D* ⊢[ x ]) , liftC₀ x
        ≈⟨ ≡→≈ (D*) (Σ≡ (rankC-beta x) ≡.refl) ⟩
      rankC₀ x , subst S̃/ (rankC-beta x) (liftC₀ x)
        ≈⟨ ≈lstep (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x)) ⟩
      α , dweaken/ (rank≤ ŝ) (subst S̃/ (rankC-beta x) (liftC₀ x))
        ≈⟨ ≈lstage α v ⟩
      α , ŝ ∎
      where
      open ≈.≈syntax {S = D*}

  isSectLiftC : ∀ (x : D*/) → D* ⊢[ liftC x ] ≡ x
  isSectLiftC = SQ.elimp (D*) (λ z → D* ⊢[ liftC z ] ≡ z) isSectLiftC₀

module Cocontinuity where
  open Rank
  open LiftElement

  ϕ₀ : FD*₀ → F.ob D*/
  ϕ₀ (α , s , f) = s , λ i → D* ⊢[ α , f i ]
  ϕ-cong : ∀ {x y : FD*₀} → Colim (FD̃/) [ x ≈ y ] → ϕ₀ x ≡ ϕ₀ y
  ϕ-cong {α , a , f̂} {α , a , f̂} (≈lstage α ≡.refl) = ≡.refl
  ϕ-cong {α , a , f̂} {β , a , ĝ} (≈lstep p (a , f̂)) =
    ≡.cong (a ,_) (funExt (λ i → D* ⊢≈[ ≈lstep p (f̂ i) ]))
  ϕ-cong {α , a , f̂} {β , b , ĝ} (≈lsym p) = ≡.sym (ϕ-cong p)
  ϕ-cong {α , a , f̂} {β , b , ĝ} (≈ltrans p q) = ≡.trans (ϕ-cong p) (ϕ-cong q)

  ϕ : Colim/ FD̃/ → F.ob D*/
  ϕ = SQ.rec FD* ϕ₀ ϕ-cong

  ϕ-beta : (x : FD*₀) → ϕ (Colim (FD̃/) ⊢[ x ]) ≡ ϕ₀ x
  ϕ-beta = SQ.rec-beta (Colim (FD̃/)) ϕ₀ ϕ-cong

  ψ : F.ob D*/ → FD*/
  ψ (s , f̂) = FD* ⊢[ α , s , x̂ ]
    where
    μ : P s → Z
    μ i = liftC (f̂ i) .proj₁
    ĝ : ∀ i → S̃/ (μ i)
    ĝ i = liftC (f̂ i) .proj₂
    α : Z
    α = Z.sup (s , μ)
    x̂ : P s → S̃/ α
    x̂ i = dweaken/ (child≤ s μ i) (ĝ i)

  ϕψ : ∀ x → ϕ (ψ x) ≡ x
  ϕψ x@(s , f̂) =
    ϕ (FD* ⊢[ α , s , x̂ ])
      ≡⟨ ϕ-beta (α , s , x̂) ⟩
    s , (λ i → D* ⊢[ α , x̂ i ])
      ≡⟨ ≡.cong (s ,_) (funExt (λ i → D* ⊢≈[ p i ])) ⟩
    s , (λ i → D* ⊢[ liftC (f̂ i) ])
      ≡⟨ ≡.cong (s ,_) (funExt (λ i → isSectLiftC (f̂ i))) ⟩
    s , f̂ ∎
    where
    μ : P s → Z
    μ i = liftC (f̂ i) .proj₁
    ĝ : ∀ i → S̃/ (μ i)
    ĝ i = liftC (f̂ i) .proj₂
    α : Z
    α = Z.sup (s , μ)
    x̂ : P s → S̃/ α
    x̂ i = dweaken/ (child≤ s μ i) (ĝ i)
    p : ∀ i → D* [ (α , x̂ i) ≈ liftC (f̂ i) ]
    p i = ≈lsym (≈lstep (child≤ s μ i) (ĝ i))
    open ≡.≡-Reasoning

  ψϕ : ∀ x → ψ (ϕ x) ≡ x
  ψϕ x = SQ.elimp FD* (λ x → ψ (ϕ x) ≡ x) p x
    where
    open ≡.≡-Reasoning
    p : ∀ (x : FD*₀) → ψ (ϕ (FD* ⊢[ x ])) ≡ FD* ⊢[ x ]
    p (α , s , f̂) =
      ψ (ϕ (FD* ⊢[ α , s , f̂ ]))
        ≡⟨ ≡.cong ψ (ϕ-beta (α , s , f̂)) ⟩
      ψ (s , λ i → D* ⊢[ α , f̂ i ])
        ≡⟨ (FD* ⊢≈[ q ]) ⟩
      (FD* ⊢[ α , s , f̂ ]) ∎
      where
      μ : P s → Z
      μ i = liftC (D* ⊢[ α , f̂ i ]) .proj₁

      β : Z
      β = Z.sup (s , μ)

      ĝ : ∀ i → S̃/ (μ i)
      ĝ i = liftC (D* ⊢[ α , f̂ i ]) .proj₂

      x̂ : P s → S̃/ β
      x̂ i = dweaken/ (child≤ s μ i) (ĝ i)

      γ : Z
      γ = α ∨ᶻ β

      h : ∀ i → dweaken/ (Z.<→≤ (Z.∨ᶻ-r< {α} {β})) (x̂ i)
              ≡ dweaken/ (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (f̂ i)
      h i =
        ≡.trans
          (≡.sym (comp (box (child≤ s μ i)) (box (Z.<→≤ (Z.∨ᶻ-r< {α} {β}))) {x = ĝ i}))
          (≡.trans
            (dweaken-cast r₁ p₁ q₁ (ĝ i))
            (≡.trans
              (≡.cong
                (dweaken/ q₁)
                (Σ-proj₂ (liftC-beta (α , f̂ i))))
              (≡.trans
                (dweaken-cast r₂ q₁ q₂ (liftC₀ (α , f̂ i)))
                (≡.trans
                  (weaken-irrel q₂ p₂ (subst S̃/ (rankC-beta (α , f̂ i)) (liftC₀ (α , f̂ i))))
                  (weakenLiftC (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (f̂ i))))))
        where
        r₁ : μ i ≡ rankC (D* ⊢[ α , f̂ i ])
        r₁ = ≡.cong proj₁ (liftC-beta (α , f̂ i))

        p₁ : μ i ≤ γ
        p₁ = ≤≤ (Z.<→≤ (Z.∨ᶻ-r< {α} {β})) (child≤ s μ i)

        q₁ : rankC (D* ⊢[ α , f̂ i ]) ≤ γ
        q₁ = ≡.substp (_≤ γ) r₁ p₁

        r₂ : rankC (D* ⊢[ α , f̂ i ]) ≡ rank (f̂ i)
        r₂ = rankC-beta (α , f̂ i)

        q₂ : rank (f̂ i) ≤ γ
        q₂ = ≡.substp (_≤ γ) r₂ q₁

        p₂ : rank (f̂ i) ≤ γ
        p₂ = ≤≤ (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (rank≤ (f̂ i))

      q : FD* [ (β , s , x̂) ≈ (α , s , f̂) ]
      q = ≈ltrans
            (≈lstep (Z.<→≤ (Z.∨ᶻ-r< {α} {β})) (s , x̂))
            (≈ltrans
              (≈lstage γ (≡.cong (s ,_) (funExt h)))
              (≈lsym (≈lstep (Z.<→≤ (Z.∨ᶻ-l< {α} {β})) (s , f̂))))

  cocontinuity : FD*/ ≅ˢ F.ob D*/ 
  cocontinuity = record
    { to = ϕ
    ; from = ψ
    ; rinv = ψϕ
    ; linv = ϕψ }
