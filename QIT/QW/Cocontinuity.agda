open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Container.Base
open import QIT.Functor.Base
open import QIT.Functor.Composition
open import QIT.Category.Base hiding (_[_≈_]; _[_,_]; _[_∘_])
open import QIT.Category.Preorder
open import QIT.Category.Setoid

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
open import QIT.Container.Functor S P ℓD ℓD'
open F-Ob

-- Size control and staging
open import QIT.Relation.Plump S P
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
Cocontinuous : (F : Functor (SetoidCat ℓc ℓc') (SetoidCat ℓc ℓc')) (D : Diagram ℓc ℓc')
              → Prop ℓc'
Cocontinuous F D =
  Colim (F ∘ D) ≅ Functor.ob F (Colim D)

module Ob = Functor F
-- F, D, and F∘D modules are already defined in StageColimit

-- Forward direction: map from Colim(F ∘ D) to ob(Colim D).
-- An element (α, (s, f)) becomes (s, λ i → (α, f i)).
ϕ₀ : ⟨ Colim (F ∘ D) ⟩ → ⟨ Ob.ob (Colim D) ⟩
ϕ₀ (α , (s , f)) = s , (λ b → α , f b)

-- Congruence for ϕ₀ at a specific stage.
ϕ-cong-stage : ∀ α {x y} → F∘D.ob α [ x ≈ y ] → Ob.ob (Colim D) [ ϕ₀ (α , x) ≈ ϕ₀ (α , y) ]
ϕ-cong-stage α {a , f} {a , g} (mk≈ꟳ ≡.refl snd≈) =
  mk≈ꟳ ≡.refl q
  where
  q : (i : P a) → Colim D [ α , f i ≈ α , g i ]
  q i = ≈lstage α u
    where
    u :  α ⊢ f i ≈ᵇ g i
    u = snd≈ i

-- Full congruence property for ϕ₀.
ϕ-cong : ∀ {x y} → Colim (F ∘ D) [ x ≈ y ] → Ob.ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
ϕ-cong (≈lstage α e) = ϕ-cong-stage α e
ϕ-cong (≈lstep {α} {j} (sup≤ p) (s , f)) =
  mk≈ꟳ ≡.refl λ k → ≈lstep (sup≤ p) (f k)
ϕ-cong (≈lsym p) = ≈fsym (Colim D) (ϕ-cong p)
ϕ-cong (≈ltrans p q) = ≈ftrans (Colim D) (ϕ-cong p) (ϕ-cong q)

-- Backward direction: map from ob(Colim D) to Colim(F ∘ D).
-- Find a common upper bound for all stages, then weaken elements to this stage.
ψ₀ : ⟨ Ob.ob (Colim D) ⟩ → ⟨ Colim (F ∘ D) ⟩
ψ₀ (s , f) = sup (ιˢ s , μ) , s , λ i → pweaken (child≤ (ιˢ s) μ i) (f i .proj₂)
  where
  μ : P s → Z
  μ i = f i .proj₁

-- Tree compatibility relation based on ordinal bounds.
_~ᵀ_ : ∀ (s t : T) → Prop _
s ~ᵀ t = ιᶻ s ≤≥ ιᶻ t

-- Strong equivalence between trees: ordinal compatibility plus provable equality.
module ≈s where
  record _≈ˢ_ (s t : T) : Prop (ℓS ⊔ ℓP ⊔ lsuc ℓV ⊔ ℓE) where
    constructor mk≈ˢ
    field
      s~t : s ~ᵀ t
      s≈t : ιᶻ s ⊢ s , ≤refl (ιᶻ s) ≈ᵇ t , s~t .∧.snd
  open _≈ˢ_ public
open ≈s hiding (s~t; s≈t)

≈srefl : ∀ {s} → s ≈ˢ s
≈srefl {s} = mk≈ˢ ≤≥-refl ≈prefl

≈ssym : ∀ {s t} → s ≈ˢ t → t ≈ˢ s
≈ssym (mk≈ˢ s~ᵀt s≈t) = mk≈ˢ (≤≥-sym s~ᵀt) (≈psym (≈pweaken (s~ᵀt .∧.fst) s≈t))

≈strans : ∀ {s t u} → s ≈ˢ t → t ≈ˢ u → s ≈ˢ u
≈strans (mk≈ˢ s~ᵀt s≈t) (mk≈ˢ t~ᵀu t≈u) =
  mk≈ˢ (≤≥-trans s~ᵀt t~ᵀu) (≈ptrans s≈t (≈pweaken (s~ᵀt .∧.snd) t≈u))

≈scong : ∀ a (f g : ∀ i → T)
       → (r : ∀ i → f i ≈ˢ g i)
       → sup (a , f) ≈ˢ sup (a , g)
≈scong a f g r = mk≈ˢ (≤≥-cong (ιˢ a) (λ α → ιᶻ (f α)) (λ α → ιᶻ (g α)) λ i → r i .≈s.s~t)
                      (≈pcong a (λ α → ιᶻ (f α))
                                (λ i → f i , ≤refl _)
                                (λ i → g i , r i .≈s.s~t .∧.snd)
                                (λ i → r i .≈s.s≈t))

-- Under the depth-preserving assumption, we can prove cocontinuity.
-- The assumption ensures equivalent elements have compatible ordinal bounds.
module _ (depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ŝ .fst ~ᵀ t̂ .fst) where

  -- Tighten stage-level relations to strong tree equivalences.
  ≈ᵇ→≈ˢ : ∀ {α ŝ t̂} → D̃ α [ ŝ ≈ t̂ ]
        → ŝ .fst ≈ˢ t̂ .fst
  ≈ᵇ→≈ˢ {α} {s , s≤α} {t , t≤α} p = u p
    where
    u : D̃ α [ s , s≤α ≈ t , t≤α ]
      → s ≈ˢ t
    u (≈pcong a μ f g r) = ≈scong a (λ i → f i .fst) (λ i → g i .fst) (λ i → ≈ᵇ→≈ˢ (r i))
    u (≈psat e ϕ l≤α r≤α) = mk≈ˢ s~ᵀt (≈psat e ϕ (≤refl (ιᶻ (lhs' e ϕ))) _)
      where
      s~ᵀt : s ~ᵀ t
      s~ᵀt = depth-preserving α (s , s≤α) (t , t≤α) p
    u ≈prefl = ≈srefl
    u (≈psym p) = ≈ssym (≈ᵇ→≈ˢ p)
    u (≈ptrans p q) = ≈strans (≈ᵇ→≈ˢ p) (≈ᵇ→≈ˢ q)
    u (≈pweaken _ p) = (≈ᵇ→≈ˢ p)

  -- Lift tightening from stage relations to colimit relations.
  ≈ˡ→≈ˢ : ∀ {ŝ t̂} → Colim D [ ŝ ≈ t̂ ]
      → ŝ .proj₂ .fst ≈ˢ t̂ .proj₂ .fst
  ≈ˡ→≈ˢ {α , s , s≤α} {α , t , t≤α} (≈lstage α p) = ≈ᵇ→≈ˢ p
  ≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈lstep p x) = ≈srefl
  ≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈lsym p) = ≈ssym (≈ˡ→≈ˢ p)
  ≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈ltrans p q) = ≈strans (≈ˡ→≈ˢ p) (≈ˡ→≈ˢ q)

  -- Congruence for ψ₀: convert colimit relations to stage relations.
  ψ-cong : ∀ {x y} → Ob.ob (Colim D) [ x ≈ y ] → Colim (F ∘ D) [ ψ₀ x ≈ ψ₀ y ]
  ψ-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = begin
    ψ₀ (s , f)
      ≈⟨ ≈lrefl (F ∘ D) ⟩
    (αf , s , λ i → tf i , _)
      ≈⟨ ≈lstep ∨ᶻ-l (s , _) ⟩
    (αf ∨ᶻ αg , s , λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ _) (fi≤μi i)))
      ≈⟨ ≈lstage (αf ∨ᶻ αg) (mk≈ꟳ ≡.refl v) ⟩
    (αf ∨ᶻ αg , s , λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ _) (gi≤μi i)))
      ≈⟨ ≈lsym (≈lstep ∨ᶻ-r (s , _)) ⟩
    (αg , s , λ i → tg i , _)
      ≈⟨ ≈lrefl (F ∘ D) ⟩
    ψ₀ (s , g) ∎
    where
    μf : P s → Z
    μf i = f i .proj₁
    μg : P s → Z
    μg i = g i .proj₁
    μ : P s → Z
    μ i = μf i ∨ᶻ μg i
    αf = sup (ιˢ s , μf)
    αg = sup (ιˢ s , μg)
    α = αf ∨ᶻ αg
    tf : P s → T
    tf i = f i .proj₂ .fst
    tg : P s → T
    tg i = g i .proj₂ .fst
    fi≤μi : ∀ i → tf i ≤ᵀ μf i
    fi≤μi i = f i .proj₂ .snd
    gi≤μi : ∀ i → tg i ≤ᵀ μg i
    gi≤μi i = g i .proj₂ .snd
    v : ∀ i → α ⊢ (tf i  , _) ≈ᵇ (tg i , _)
    v i = ≈pweaken (≤≤ μi≤α (≤≤ ∨ᶻ-l (fi≤μi i))) (≈ˡ→≈ˢ (snd≈ i) .≈s.s≈t)
      where
      μi≤α : μ i ≤ α
      μi≤α = ∨ᶻ≤ (<≤ ∨ᶻ-l< (child≤ (ιˢ s) μf i)) (<≤ ∨ᶻ-r< (child≤ (ιˢ s) μg i))
    open ≈.Hom
    open Setoid (Colim (F ∘ D))
    open ≈.≈syntax {S = Colim (F ∘ D)}

  -- Left inverse: ϕ₀ ∘ ψ₀ ≈ id on ob(Colim D).
  linv : ∀ y → Ob.ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
  linv (s , g) =
    ϕ₀ (ψ₀ (s , g))
      ≈⟨ ≈frefl (Colim D) ⟩
    (s , λ i → sup (ιˢ s , λ i → g i .proj₁) , pweaken (child≤ (ιˢ s) μ i) (g i .proj₂))
      ≈⟨ mk≈ꟳ ≡.refl (λ i → ≈lsym (≈lstep (child≤ (ιˢ s) μ i) (g i .proj₂))) ⟩
    (s , g) ∎
    where
    μ : P s → Z
    μ i = g i .proj₁
    open Setoid (Ob.ob (Colim D))
    open ≈.≈syntax {S = (Ob.ob (Colim D))}

  -- Right inverse: ψ₀ ∘ ϕ₀ ≈ id on Colim(F ∘ D).
  rinv : ∀ x → Colim (F ∘ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
  rinv (α , (s , g)) = begin
    ψ₀ (ϕ₀ (α , (s , g)))
      ≈⟨ refl ⟩
    α' , (s , λ i → pweaken (child≤ (ιˢ s) (λ _ → α) i) (g i))
      ≈⟨ (≈lstep ∨ᶻ-r (s , (λ i → pweaken ((child≤ (ιˢ s) (λ _ → α) i)) (g i)))) ⟩
    α ∨ᶻ α' , (s , λ i → pweaken (≤≤ ∨ᶻ-r (child≤ (ιˢ s) (λ _ → α) i)) (g i))
      ≈⟨ refl ⟩
    α ∨ᶻ α' , (s , λ i → pweaken ∨ᶻ-l (g i))
      ≈⟨ sym (≈lstep ∨ᶻ-l (s , g)) ⟩
    α , (s , g) ∎
    where
    α' = sup (ιˢ s , λ _ → α)
    β = α ∨ᶻ α'
    open Setoid (Colim (F ∘ D))
    open ≈.≈syntax {S = Colim (F ∘ D)}

  -- Main result: container functors are cocontinuous under depth preservation.
  depthPrserving→cocontinuous : Cocontinuous F D
  depthPrserving→cocontinuous = ∣ iso ∣
    where
    iso : ≈.Iso (Colim (F ∘ D)) (Ob.ob (Colim D))
    iso = record
      { ⟦_⟧ = ϕ₀
      ; ⟦_⟧⁻¹ = ψ₀
      ; cong = ϕ-cong
      ; cong⁻¹ = ψ-cong
      ; linv = linv
      ; rinv = rinv
      }
