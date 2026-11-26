open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Set.Base
open import QIT.Relation.SetQuotient
import QIT.SimpleDiagram

module QIT.Colimit.Properties
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq : SetQuotients ⦄
  {ℓI} {ℓ<}
  {I : Set ℓI}
  (<p : WeakPreorder I ℓ<)
  (ℓD : Level)
  (P : QIT.SimpleDiagram.Diagram {ℓA = ℓI} {ℓ< = ℓ<} {A = I} <p ℓD)
  where

open FunExt funExt*

open import QIT.Setoid
open import QIT.Setoid.Quotient

private
  module < = IsWeakPreorder (<p .proj₂)
  _<_ : BinaryRel I ℓ<
  _<_ = <p .proj₁

open import QIT.SimpleDiagram <p
open import QIT.Colimit.Base <p ℓD P public

P̂ : I → Set ℓD
P̂ = Diagram.ob P

Below : I → Set (ℓI ⊔ ℓ<)
Below α = ΣP I (_< α)

_<↓_ : ∀ {α} → BinaryRel (Below α) ℓ<
(i , _) <↓ (j , _) = i < j

Restrict< : (α : I) → WeakPreorder (Below α) ℓ<
Restrict< α = _<↓_ , record { trans = <.trans }

RestrictDiagram : (α : I) → QIT.SimpleDiagram.Diagram (Restrict< α) ℓD
RestrictDiagram α = record
  { ob = λ i → P.ob (i .fst)
  ; edge = P.edge
  ; nat = P.nat }

module Bounded (α : I) where
  open import QIT.Colimit.Base (Restrict< α) ℓD (RestrictDiagram α) public
    using ()
    renaming
      ( Colim₀ to Colim≤₀
      ; _≈ˡ_ to _≈ˡ≤_
      ; recˡ to recˡ≤
      ; ≈lrefl to ≈lrefl≤
      ; Colim to Colim≤~
      ; Colim/ to Colim≤
      ; ≈lstage to ≈l≤stage
      ; ≈lstep to ≈l≤step
      ; ≈lsym to ≈l≤sym
      ; ≈ltrans to ≈l≤trans
      )

  forget₀ : Colim≤₀ → Colim₀
  forget₀ (i≤α , x) = i≤α .fst , x

  forget≈≤ : ∀ {s t} → s ≈ˡ≤ t → forget₀ s ≈ˡ forget₀ t
  forget≈≤ (≈lstage i e) = ≈lstage (i .fst) e
  forget≈≤ (≈lstep p x) = ≈lstep p x
  forget≈≤ (≈lsym r) = ≈lsym (forget≈≤ r)
  forget≈≤ (≈ltrans r₁ r₂) = ≈ltrans (forget≈≤ r₁) (forget≈≤ r₂)

  recˡ≤' : ∀ {ℓ ℓ'}
        → (C≤ : ∀ {s t} → s ≈ˡ≤ t → Prop ℓ)
        → (C  : ∀ {s t} → s ≈ˡ t → Prop ℓ')
        → (c-stage : ∀ (i : Below α) {x x'} (e : x ≡ x') → C≤ (≈l≤stage i e))
        → (c-step  : ∀ {i j : Below α} (p : i .fst < j .fst) (x : P̂ (i .fst)) → C≤ (≈l≤step p x))
        → (c-sym   : ∀ {s t} (r : s ≈ˡ≤ t) → C≤ r → C≤ (≈l≤sym r))
        → (c-trans : ∀ {s t u} (r₁ : s ≈ˡ≤ t) (r₂ : t ≈ˡ≤ u) → C≤ r₁ → C≤ r₂ → C≤ (≈l≤trans r₁ r₂))
        → (forgetC : ∀ {s t} (r : s ≈ˡ≤ t) → C≤ r → C (forget≈≤ r))
        → ∀ {s t} (r : s ≈ˡ≤ t) → C (forget≈≤ r)
  recˡ≤' C≤ C c-stage c-step c-sym c-trans forgetC r = forgetC r (go r)
    where
    go : ∀ {s t} (r : s ≈ˡ≤ t) → C≤ r
    go (≈lstage i e) = c-stage i e
    go (≈lstep {i} {j} p x) = c-step {i} {j} p x
    go (≈lsym r) = c-sym r (go r)
    go (≈ltrans r₁ r₂) = c-trans r₁ r₂ (go r₁) (go r₂)

record BoundedFactor (s t : Colim₀) : Set (ℓI ⊔ ℓ< ⊔ ℓD) where
  field
    α : I
    s≤α : s .proj₁ < α
    t≤α : t .proj₁ < α
    r≤ : let module B = Bounded α in B._≈ˡ≤_ ((s .proj₁ , s≤α) , s .proj₂) ((t .proj₁ , t≤α) , t .proj₂)

recˡ↑ : ∀ {ℓ≤' ℓ}
      → (C : ∀ {s t} → s ≈ˡ t → Prop ℓ)
      → (factor : ∀ {s t} (r : s ≈ˡ t) → BoundedFactor s t)
      → (C≤ : ∀ α {s t} → let module B = Bounded α in B._≈ˡ≤_ s t → Prop ℓ≤')
      → (c-stage : ∀ α (i : Below α) {x x'} (e : x ≡ x') → C≤ α (Bounded.≈l≤stage {α = α} i e))
      → (c-step  : ∀ α {i j : Below α} (p : i .fst < j .fst) (x : P̂ (i .fst))
                → C≤ α (Bounded.≈l≤step {α = α} {i = i} {j = j} p x))
      → (c-sym   : ∀ α {s t} (r : let module B = Bounded α in B._≈ˡ≤_ s t)
                → C≤ α r → C≤ α (Bounded.≈l≤sym {α = α} r))
      → (c-trans : ∀ α {s t u}
                (r₁ : let module B = Bounded α in B._≈ˡ≤_ s t)
                (r₂ : let module B = Bounded α in B._≈ˡ≤_ t u)
                → C≤ α r₁ → C≤ α r₂ → C≤ α (Bounded.≈l≤trans {α = α} r₁ r₂))
      → (forgetC : ∀ α {s t} (r : let module B = Bounded α in B._≈ˡ≤_ s t)
                → C≤ α r → C (Bounded.forget≈≤ α r))
      → (stable : ∀ {s t} (p q : s ≈ˡ t) → C q → C p)
      → ∀ {s t} (r : s ≈ˡ t) → C r
recˡ↑ C factor C≤ c-stage c-step c-sym c-trans forgetC stable r =
  stable r (B.forget≈≤ (F.r≤)) pr
  where
  f = factor r
  module F = BoundedFactor f
  module B = Bounded (F.α)
  pr : C (B.forget≈≤ (F.r≤))
  pr = B.recˡ≤' (C≤ (F.α)) C (c-stage (F.α)) (c-step (F.α)) (c-sym (F.α)) (c-trans (F.α)) (forgetC (F.α)) (F.r≤)

record Cocone : Set (lsuc (ℓ< ⊔ ℓD ⊔ ℓI)) where
  field
    Apex     : Set (ℓI ⊔ ℓ< ⊔ ℓD)
    inj      : ∀ i → P̂ i → Apex
    commutes : ∀ {i j} (p : i < j)
              → inj i ≡ (inj j ∘ P.edge p)

open Cocone

LimitCocone : Cocone
LimitCocone = record
  { Apex     = Colim /≈
  ; inj      = λ i x → Colim ⊢[ i , x ]
  ; commutes = λ p → funExt λ x → Colim ⊢≈[ ≈lstep p x ]
  }

record ColimMorphism (C C' : Cocone) : Set (ℓI ⊔ ℓ< ⊔ ℓD) where
  field
    apexHom  : (C .Apex) → (C' .Apex)
    commutes : ∀ i → (apexHom ∘ C .inj i) ≡ (C' .inj i)

open ColimMorphism

record isLimitingCocone (C : Cocone) : Set (lsuc ℓI ⊔ lsuc ℓ< ⊔ lsuc ℓD) where
  field
    hom    : ∀ C' → ColimMorphism C C'
    unique : ∀ C' → (F : ColimMorphism C C')
            → ∀ x̃ → F .apexHom x̃ ≡ hom C' .apexHom x̃

module IsLimitingCocone (C' : Cocone) where
  module C' = Cocone C'

  open isLimitingCocone
  open ≈.Hom
  module Colim/≈ = SQ Colim

  f₀ : Colim₀ → C'.Apex
  f₀ (i , x) = C'.inj i x

  isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y) → f₀ (i , x) ≡ f₀ (j , y)
  isRespecting (≈lstage i x≈y) = ≡.cong (C'.inj i) x≈y
  isRespecting {i} {j} {x} {y} (≈lstep p x) = ≡.funExt⁻ (C'.commutes p) x
  isRespecting (≈lsym r) = ≡.sym (isRespecting r)
  isRespecting (≈ltrans r s) = ≡.trans (isRespecting r) (isRespecting s)

  f : Colim /≈ → C'.Apex
  f = Colim/≈.rec f₀ isRespecting

  F : ColimMorphism LimitCocone C'
  F .apexHom = f
  F .commutes i = funExt λ x → Colim/≈.rec-beta f₀ isRespecting (i , x)

  unq : (G : ColimMorphism LimitCocone C') → ∀ x̃ → G .apexHom x̃ ≡ f x̃
  unq G = Colim/≈.elimp (λ x̃ → G .apexHom x̃ ≡ f x̃) λ (i , x) →
    ≡.trans (≡.funExt⁻ (G .commutes i) x)
            (≡.sym (Colim/≈.rec-beta f₀ isRespecting (i , x)))

isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
isLimitingCoconeLimitCocone = record
  { hom    = F
  ; unique = unq
  }
  where
  open IsLimitingCocone
