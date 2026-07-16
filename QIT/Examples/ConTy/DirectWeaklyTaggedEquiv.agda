open import QIT.Prelude

module QIT.Examples.ConTy.DirectWeaklyTaggedEquiv
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

open import QIT.Examples.ConTy.DirectToWeaklyTaggedLarge
open import QIT.Examples.ConTy.WeaklyTaggedToDirect

open import QIT.Prelude
open import QIT.Prop
open import QIT.Types
open import QIT.Maybe
open import QIT.Setoid hiding (≡→≈)
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Category.Base
open import QIT.Functor.NatTrans 
open import QIT.Functor.Properties
open import QIT.PropLiftMonad

ε : ∀ {ℓA} (A : D.Algebra ℓA) → D.Hom (F₀ (G₀ A)) A
ε {ℓA} A = record
  { conᴿ = conᴿ
  ; tyᴿ = tyᴿ
  ; ∙ᴿ = ≡.refl
  ; ▷ᴿ = λ _ _ → ≡.refl
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module ε where
  module DA = D.Algebra A
  module G = G₀ A
  module WGA = W.Algebra (G₀ A)
  module FGA = F₀ (G₀ A)
  module DFA = D.Algebra (F₀ (G₀ A))

  conAtom : DFA.Con → G.Atom
  conAtom (γ , kγ) = γ .val (G.conData₁ γ kγ)

  conAtom-isCon : (γ : DFA.Con) → G.[ conAtom γ ]₀ ≡ G.ĉ
  conAtom-isCon (γ , kγ) = G.conData₂ γ kγ

  conᴿ : DFA.Con → DA.Con
  conᴿ γ = G.Con₀ (conAtom γ) (conAtom-isCon γ)

  tyAtom : (γ : DFA.Con) → DFA.Ty γ → G.Atom
  tyAtom (γ , kγ) (a , ka) = a .val (G.tyData₁ γ a kγ ka)

  tyAtom-isTy : (γ : DFA.Con) (a : DFA.Ty γ)
    → G.[ tyAtom γ a ]₀ ≡ G.t̂ (conAtom γ)
  tyAtom-isTy (γ , kγ) (a , ka) = G.tyData₂ γ a kγ ka

  tyᴿ : (γ : DFA.Con) → DFA.Ty γ → DA.Ty (conᴿ γ)
  tyᴿ γ a = G.Ty₀ (conAtom γ) (tyAtom γ a) (conAtom-isCon γ) (tyAtom-isTy γ a)

  u₀ : (γ : G.Atom) (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → G.Ty₀ γ (G.u₀ γ kγ) kγ (G.ku₀ γ kγ) ≡ DA.u (G.Con₀ γ kγ)
  u₀ (G.con γ) ≡.refl = ≡.refl

  uᴿ : (γ : DFA.Con) → tyᴿ γ (DFA.u γ) ≡ DA.u (conᴿ γ)
  uᴿ γ = u₀ (conAtom γ) (conAtom-isCon γ)

  πᴿ : (γ : DFA.Con) (a : DFA.Ty γ) (b : DFA.Ty (γ DFA.▷ a))
    → tyᴿ γ (DFA.π γ a b) ≡ DA.π (conᴿ γ) (tyᴿ γ a) (tyᴿ (γ DFA.▷ a) b)
  πᴿ γ a b =
    G.Ty₀-π₀ (conAtom γ) (tyAtom γ a) (tyAtom (γ DFA.▷ a) b)
      (conAtom-isCon γ) (tyAtom-isTy γ a) (tyAtom-isTy (γ DFA.▷ a) b)

  σᴿ : (γ : DFA.Con) (a : DFA.Ty γ) (b : DFA.Ty (γ DFA.▷ a))
    → tyᴿ γ (DFA.σ γ a b) ≡ DA.σ (conᴿ γ) (tyᴿ γ a) (tyᴿ (γ DFA.▷ a) b)
  σᴿ γ a b =
    G.Ty₀-σ₀ (conAtom γ) (tyAtom γ a) (tyAtom (γ DFA.▷ a) b)
      (conAtom-isCon γ) (tyAtom-isTy γ a) (tyAtom-isTy (γ DFA.▷ a) b)

ε⁻ : ∀ {ℓA} (A : D.Algebra ℓA) → D.Hom A (F₀ (G₀ A))
ε⁻ A = record
  { conᴿ = conᴿ
  ; tyᴿ = tyᴿ
  ; ∙ᴿ = ∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module ε⁻ where
  module DA = D.Algebra A
  module G = G₀ A
  module DFA = D.Algebra (F₀ (G₀ A))
  module FGA = F₀ (G₀ A)

  ι : G.Atom → G.CT
  ι x = ⊤* ⊢ λ _ → x

  kcon : (γ : DA.Con) → G.[ ι (G.con γ) ] ≡ G.cʰ
  kcon γ = mk≡↓ (∧i tt* , tt*) tt* ≡.refl

  kty : (γ : DA.Con) (a : DA.Ty γ) → G.[ ι (G.ty γ a) ] ≡ G.tʰ (ι (G.con γ))
  kty γ a = G.mkCT≡ (λ p → p) (λ p → p) λ _ _ → ≡.refl

  ▷ι : (γ : DA.Con) (a : DA.Ty γ) → G.▷ (ι (G.con γ)) (ι (G.ty γ a)) ≡ ι (G.con (γ DA.▷ a))
  ▷ι γ a = mk≡↓ q tt* ≡.refl
    where
    q : G.▷ (ι (G.con γ)) (ι (G.ty γ a)) ↓
    q = ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , tt*

  uι : (γ : DA.Con) → G.u (ι (G.con γ)) ≡ ι (G.ty γ (DA.u γ))
  uι γ = mk≡↓ q tt* ≡.refl
    where
    q : G.u (ι (G.con γ)) .Cond
    q = ∧i tt* , ∧i ≡.refl , tt*

  πι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.π γ a b))
  πι γ a b = mk≡↓ q tt* ≡.refl
    where
    q : G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) .Cond
    q = ∧i tt* , ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , ∧i ≡.refl , tt*

  σι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.σ γ a b))
  σι γ a b = mk≡↓ q tt* ≡.refl
    where
    q : G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) .Cond
    q = ∧i tt* , ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , ∧i ≡.refl , tt*

  conᴿ : DA.Con → DFA.Con
  conᴿ γ = ι (G.con γ) , kcon γ

  tyᴿ : (γ : DA.Con) → DA.Ty γ → DFA.Ty (conᴿ γ)
  tyᴿ γ a = ι (G.ty γ a) , kty γ a

  ∙ᴿ : conᴿ DA.∙ ≡ DFA.∙
  ∙ᴿ = ΣP≡ _ _ ≡.refl

  ▷ᴿ : ∀ γ a → conᴿ (γ DA.▷ a) ≡ conᴿ γ DFA.▷ tyᴿ γ a
  ▷ᴿ γ a = ΣP≡ _ _ (≡.sym (▷ι γ a))

  uᴿ : ∀ γ → tyᴿ γ (DA.u γ) ≡ DFA.u (conᴿ γ)
  uᴿ γ = ΣP≡ _ _ (≡.sym (uι γ))

  πᴿ : ∀ γ a b → tyᴿ γ (DA.π γ a b)
    ≡ DFA.π (conᴿ γ) (tyᴿ γ a) (subst DFA.Ty (▷ᴿ γ a) (tyᴿ (γ DA.▷ a) b))
  πᴿ γ a b = ΣP≡ _ _ p
    where
    p = ≡.trans (≡.sym (πι γ a b))
        (≡.cong (G.π (ι (G.con γ)) (ι (G.ty γ a)))
                (≡.sym (FGA.Ty-fst (▷ᴿ γ a))))

  σᴿ : ∀ γ a b → tyᴿ γ (DA.σ γ a b)
    ≡ DFA.σ (conᴿ γ) (tyᴿ γ a) (subst DFA.Ty (▷ᴿ γ a) (tyᴿ (γ DA.▷ a) b))
  σᴿ γ a b = ΣP≡ _ _ p
    where
    p = ≡.trans (≡.sym (σι γ a b))
        (≡.cong (G.σ (ι (G.con γ)) (ι (G.ty γ a)))
                (≡.sym (FGA.Ty-fst (▷ᴿ γ a))))

εε⁻ : ∀ {ℓA} (A : D.Algebra ℓA) → (ε A D.∘ ε⁻ A) D.≈ D.id
εε⁻ A = D.mk≈ con≡ ty≡
  where
  module A = D.Algebra A
  con≡ : (γ : A.Con) → (ε A D.∘ ε⁻ A) .D.conᴿ  γ ≡ D.conᴿ (D.id {A = A}) γ
  con≡ γ = ≡.refl
  ty≡ : (γ : A.Con) (a : A.Ty γ)
      → ≡.subst A.Ty (con≡ γ) (D.tyᴿ (ε A D.∘ ε⁻ A) γ a)
      ≡ D.tyᴿ (D.id {A = A}) γ a
  ty≡ γ a = ≡.refl


ε⁻ε : ∀ {ℓA} (A : D.Algebra ℓA) → (ε⁻ A D.∘ ε A) D.≈ D.id
ε⁻ε A = D.mk≈ con≡ ty≡
  where
  module DA = D.Algebra A
  module G = G₀ A
  module FG = F₀ (G₀ A)
  module DFA = D.Algebra (F₀ (G₀ A))

  ι : G.Atom → G.CT
  ι = ε⁻.ι A

  inhabited→ι : (x : G.CT) → (p : x .Cond) → x ≡ ι (x .val p)
  inhabited→ι (P ⊢ f) p = G.mkCT≡ (λ _ → tt*) (λ _ → p) (λ q _ → ≡.congp f)

  Ty₀-η : (γ a : G.Atom)
    → (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → (ka : G.[ a ]₀ ≡ G.t̂ γ)
    → G.ty (G.Con₀ γ kγ) (G.Ty₀ γ a kγ ka) ≡ a
  Ty₀-η (G.con γ) (G.ty .γ a) ≡.refl ≡.refl = ≡.refl

  con≡ : (γ : DFA.Con) → (ε⁻ A D.∘ ε A) .D.conᴿ γ ≡ D.conᴿ (D.id {A = F₀ (G₀ A)}) γ
  con≡ γ@(x , kx) = ΣP≡ _ _ p
    where
    witness : x ↓
    witness = G.conData₁ x kx
    p : ι (G.con (ε.conᴿ A γ)) ≡ x
    p =
      ≡.trans
        (≡.cong ι (G.con-Con₀ (ε.conAtom A γ) (ε.conAtom-isCon A γ)))
        (≡.sym (inhabited→ι x witness))

  ty≡ : (γ : DFA.Con) (a : DFA.Ty γ)
      → subst DFA.Ty (con≡ γ) (D.tyᴿ (ε⁻ A D.∘ ε A) γ a)
      ≡ D.tyᴿ (D.id {A = F₀ (G₀ A)}) γ a
  ty≡ γ@(x , kx) a@(y , ky) = ΣP≡ _ _ p
    where
    witness : y .Cond
    witness = G.tyData₁ x y kx ky
    q : ι (G.ty (ε.conᴿ A γ) (ε.tyᴿ A γ a)) ≡ y
    q =
      ≡.trans
        (≡.cong ι
          (Ty₀-η (ε.conAtom A γ) (ε.tyAtom A γ a)
                 (ε.conAtom-isCon A γ) (ε.tyAtom-isTy A γ a)))
        (≡.sym (inhabited→ι y witness))
    p : subst DFA.Ty (con≡ γ) (D.tyᴿ (ε⁻ A D.∘ ε A) γ a) .fst ≡ y
    p = ≡.trans (FG.Ty-fst (con≡ γ)) q

ε' : ∀ {ℓA} (A : D.Algebra ℓA) → D.Hom (F₀ (G₀ A)) (D.LiftAlgebra (lsuc ℓA) A)
ε' {ℓA} A = D.Lift⇒ (lsuc ℓA) A D.∘ ε A

ε⁻' : ∀ {ℓA} (A : D.Algebra ℓA) → D.Hom (D.LiftAlgebra (lsuc ℓA) A) (F₀ (G₀ A))
ε⁻' {ℓA} A = ε⁻ A D.∘ D.Lift⇐ (lsuc ℓA) A

isIso-ε' : ∀ {ℓA} (A : D.Algebra ℓA) → IsIso (D.Cat (lsuc ℓA)) (ε' A)
isIso-ε' {ℓA} A = record
  { f⁻¹ = ε⁻' A
  ; linv = linv
  ; rinv = rinv }
  where
  -- These composites reduce definitionally:
  -- (ε⁻' ∘ ε') = (ε⁻ ∘ ε), and (ε' ∘ ε⁻') = (Lift⇒ ∘ Lift⇐).
  linv : (ε⁻' A D.∘ ε' A) D.≈ D.id
  linv = ε⁻ε A
  rinv : (ε' A D.∘ ε⁻' A) D.≈ D.id
  rinv = D.Lift⇒⇐ (lsuc ℓA) A

module _ {ℓA}
  (Iᵂ : W.Algebra (lsuc ℓA))
  (recᵂ : (Aᵂ : W.Algebra (lsuc ℓA)) → W.Hom Iᵂ Aᵂ)
  (recUniqueᵂ : {Aᵂ : W.Algebra (lsuc ℓA)} → (f : W.Hom Iᵂ Aᵂ) → f W.≈ recᵂ Aᵂ)
  where

  Iᴰ : D.Algebra (lsuc ℓA)
  Iᴰ = F₀ Iᵂ
  module Iᵂ = W.Algebra Iᵂ
  module Iᴰ = D.Algebra Iᴰ

  h : (Aᴰ : D.Algebra ℓA) → W.Hom Iᵂ (G₀ Aᴰ) 
  h Aᴰ = recᵂ (G₀ Aᴰ)

  recᴰ : (Aᴰ : D.Algebra ℓA) → D.Hom Iᴰ Aᴰ
  recᴰ Aᴰ = ε Aᴰ D.∘ F₁ (h Aᴰ)

  module _ {Aᴰ : D.Algebra ℓA} (fᴰ : D.Hom {ℓA = lsuc ℓA} (F₀ Iᵂ) (F₀ (G₀ Aᴰ))) where
    ℓA' = lsuc ℓA
    ℓA'' = lsuc ℓA'
    module fᴰ = D.Hom fᴰ
    module Aᴰ = D.Algebra Aᴰ
    Aᴰ↑ = D.LiftAlgebra ℓA' Aᴰ
    module Aᴰ↑ = D.Algebra (D.LiftAlgebra ℓA' Aᴰ)

    module G₀Aᴰ = G₀ Aᴰ
    module GAᴰ = W.Algebra (G₀ Aᴰ)

    r : W.Hom {ℓA = ℓA'} Iᵂ (G₀ Aᴰ)
    r = recᵂ (G₀ Aᴰ)

    module r = W.Hom r
    module Fr = F₁ r
    open ≡.≡-Reasoning

    θkγ : (γ : Iᵂ.CT)
        → Iᵂ.[ γ ] ≡ Iᵂ.ĉ
        → G₀Aᴰ.[ r.θ γ ] ≡ G₀Aᴰ.cʰ
    θkγ γ kγ =
      G₀Aᴰ.[ r.θ γ ]
        ≡⟨ ≡.sym r.[ γ ] ⟩
      r.θ Iᵂ.[ γ ]
        ≡⟨ ≡.cong r.θ kγ ⟩
      r.θ Iᵂ.ĉ
        ≡⟨ r.ĉ ⟩
      G₀Aᴰ.cʰ ∎

    θka : (γ a : Iᵂ.CT)
        → Iᵂ.[ γ ] ≡ Iᵂ.ĉ
        → Iᵂ.[ a ] ≡ Iᵂ.t̂ γ
        → G₀Aᴰ.[ r.θ a ] ≡ G₀Aᴰ.tʰ (r.θ γ)
    θka γ a kγ ka =
      G₀Aᴰ.[ r.θ a ]
        ≡⟨ ≡.sym r.[ a ] ⟩
      r.θ Iᵂ.[ a ]
        ≡⟨ ≡.cong r.θ ka ⟩
      r.θ (Iᵂ.t̂ γ)
        ≡⟨ r.t̂ γ ⟩
      G₀Aᴰ.tʰ (r.θ γ) ∎

    conM : ∀ (γ : Iᵂ.CT)
      → (kγ : Iᵂ.[ γ ] ≡ Iᵂ.ĉ)
      → {!Aᴰ.Con!}
    conM γ kγ = G₀Aᴰ.conData₁ (r.θ γ) {!!}

    η : D.Hom (F₀ Iᵂ) Aᴰ
    η .D.conᴿ (γ , kγ) =
      {!!}
      where
      cd₁ = G₀Aᴰ.conData₁ {!γ!}
    η .D.tyᴿ (γ , kγ) (a , ka) =
      {!!} 
    η .D.∙ᴿ = {!!}
    η .D.▷ᴿ = {!!}
    η .D.uᴿ = {!!}
    η .D.πᴿ = {!!}
    η .D.σᴿ = {!!}

    η↑ : D.Hom (F₀ Iᵂ) Aᴰ↑
    η↑ = D.Lift⇒ ℓA' Aᴰ D.∘ η

    τ : W.Hom {ℓA = lsuc (lsuc ℓA)} (G₀ (F₀ Iᵂ)) (G₀ Aᴰ↑)
    τ = G₁ {!!}

    beta : F₁ r D.≈ fᴰ
    beta =
      D.mk≈ {!con≡!} {!ty≡!}
      where

      conEq : (γ : Iᵂ.CT) → Iᵂ.[ γ ] ≡ Iᵂ.ĉ → G₀Aᴰ.[ r.θ γ ] ≡ G₀Aᴰ.cʰ
      conEq γ kγ =
        G₀Aᴰ.[ r.θ γ ]
          ≡⟨ ≡.sym (r.[ γ ]) ⟩
        r.θ Iᵂ.[ γ ]
          ≡⟨ ≡.cong r.θ kγ ⟩
        r.θ Iᵂ.ĉ
          ≡⟨ r.ĉ ⟩
        G₀Aᴰ.cʰ ∎
        where open ≡.≡-Reasoning

      conDef : (γ : Iᵂ.CT) → Iᵂ.[ γ ] ≡ Iᵂ.ĉ → r.θ γ ↓
      conDef γ kγ = (≡→≈ (conEq γ kγ) .∧e₁ .∧e₂ tt*) .∧e₂

      tyEq : (γ a : Iᵂ.CT)
        → Iᵂ.[ γ ] ≡ Iᵂ.ĉ
        → Iᵂ.[ a ] ≡ Iᵂ.t̂ γ
        → G₀Aᴰ.[ r.θ a ] ≡ G₀Aᴰ.tʰ (r.θ γ)
      tyEq γ a kγ ka =
        G₀Aᴰ.[ r.θ a ]
          ≡⟨ ≡.sym (r.[ a ]) ⟩
        r.θ Iᵂ.[ a ]
          ≡⟨ ≡.cong r.θ ka ⟩
        r.θ (Iᵂ.t̂ γ)
          ≡⟨ r.t̂ γ ⟩
        G₀Aᴰ.tʰ (r.θ γ) ∎
        where open ≡.≡-Reasoning

      tyDef : (γ a : Iᵂ.CT)
        → Iᵂ.[ γ ] ≡ Iᵂ.ĉ
        → Iᵂ.[ a ] ≡ Iᵂ.t̂ γ
        → r.θ a ↓
      tyDef γ a kγ ka =
        (≡→≈ (tyEq γ a kγ ka) .∧e₁ .∧e₂ (∧i tt* , conDef γ kγ)) .∧e₂

      conRet : (γ : Iᵂ.CT)
        → Iᵂ.[ γ ] ≡ Iᵂ.ĉ
        → ΣP Aᴰ.Con λ γ₀ → r.θ γ ≡ return (G₀Aᴰ.con γ₀)
      conRet γ kγ = G₀Aᴰ.[]≡cʰ→return (conEq γ kγ)

      tyRet : (γ a : Iᵂ.CT)
        → (kγ : Iᵂ.[ γ ] ≡ Iᵂ.ĉ)
        → (ka : Iᵂ.[ a ] ≡ Iᵂ.t̂ γ)
        → Σ Aᴰ.Con λ γ₀
        → ΣP (Aᴰ.Ty γ₀) λ a₀
        → r.θ a ≡ return (G₀Aᴰ.ty γ₀ a₀)
        ∧ r.θ γ ≡ return (G₀Aᴰ.con γ₀)
      tyRet γ a kγ ka = G₀Aᴰ.[]≡tʰ→return (tyEq γ a kγ ka) (tyDef γ a kγ ka)

      ▷-inv : (γ a : Iᵂ.CT)
        → (kγ : Iᵂ.[ γ ] ≡ Iᵂ.ĉ)
        → (ka : Iᵂ.[ a ] ≡ Iᵂ.t̂ γ)
        → (▷↓ : r.θ (Iᵂ.▷ γ a) ↓)
        → r.θ γ ↓
        ∧ r.θ a ↓
      ▷-inv γ a kγ ka ▷↓ = ∧i γ↓ , a↓
        where
        ▷↓' : G₀Aᴰ.▷ (r.θ γ) (r.θ a) ↓
        ▷↓' = ≡.substp (_↓) (r.▷ γ a kγ ka) ▷↓
        γ↓ : r.θ γ ↓
        γ↓ = G₀Aᴰ.▷⁻-γ (r.θ γ) (r.θ a) ▷↓'
        a↓ : r.θ a ↓
        a↓ = G₀Aᴰ.▷⁻-a (r.θ γ) (r.θ a) ▷↓'

      record P (x : Iᵂ.CT) : Prop (lsuc ℓA) where
        field
          Conβ :
            (kx : Iᵂ.[ x ] ≡ Iᵂ.ĉ)
            → r.θ x ≡ fᴰ.conᴿ (x , kx) .fst
          Tyβ : 
            (γ : Iᵂ.CT)
            → (kγ : Iᵂ.[ γ ] ≡ Iᵂ.ĉ)
            → (kx : Iᵂ.[ x ] ≡ Iᵂ.t̂ γ)
            → r.θ x ≡ fᴰ.tyᴿ (γ , kγ) (x , kx) .fst
          ▷-con-γ : ∀ γ a
            → x ≡ Iᵂ.▷ γ a
            → Iᵂ.[ Iᵂ.▷ γ a ] ≡ Iᵂ.ĉ
            → Iᵂ.[ γ ] ≡ Iᵂ.ĉ
          ▷-con-a : ∀ γ a
            → x ≡ Iᵂ.▷ γ a
            → Iᵂ.[ Iᵂ.▷ γ a ] ≡ Iᵂ.ĉ
            → Iᵂ.[ a ] ≡ Iᵂ.t̂ γ
          ▷-ty-absurd : ∀ γ a δ
            → x ≡ Iᵂ.▷ γ a
            → (kγ : Iᵂ.[ γ ] ≡ Iᵂ.ĉ)
            → (ka : Iᵂ.[ a ] ≡ Iᵂ.t̂ δ)
            → Iᵂ.[ Iᵂ.▷ γ a ] ≡ Iᵂ.t̂ δ
            → ⊥
          u-con-absurd : ∀ {γ}
            → Iᵂ.[ Iᵂ.u γ ] ≡ Iᵂ.ĉ
            → ⊥
          u-ty-inv : ∀ {γ γ'}
            → Iᵂ.[ Iᵂ.u γ ] ≡ Iᵂ.t̂ γ'
            → Iᵂ.[ γ ] ≡ Iᵂ.ĉ ∧ᵖ λ _ → γ' ≡ γ

      Pᵂ : W.Algebra (lsuc ℓA)
      Pᵂ = record
        { CT = CT
        ; [_] = [_]
        -- ; k̂ = k̂
        -- ; kk̂ = kk̂
        -- ; ĉ = ĉ
        -- ; kĉ = kĉ
        -- ; t̂ = t̂
        -- ; kt̂ = kt̂
        -- ; ∙ = ∙
        -- ; k∙ = k∙
        -- ; ▷ = ▷
        -- ; k▷ = k▷
        -- ; u = u
        -- ; ku = ku
        -- ; π = π
        -- ; kπ = kπ
        -- ; σ = σ
        -- ; kσ = kσ
        -- ; σ▷ = σ▷
        -- ; σπ = σπ
        }
        where
        CT : Set (lsuc ℓA)
        CT = ΣP Iᵂ.CT P

        open P

        [_] : CT → CT
        [ x , px ] = Iᵂ.[ x ] , p
          where
          p : P Iᵂ.[ x ]
          p .Conβ kx = ⊥e (G₀Aᴰ.[[x]]≢cʰ {x* = r.θ x} q)
            where
            q : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.cʰ
            q = ≡.trans (≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ])) (conEq (Iᵂ.[ x ]) kx)
          p .Tyβ γ kγ kx = ⊥e (G₀Aᴰ.[[x]]≢tʰ {r.θ x} {r.θ γ} x↓ q)
            where
            γ↓ : r.θ γ ↓
            γ↓ = conDef γ kγ

            q : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.tʰ (r.θ γ)
            q = ≡.trans (≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ])) (tyEq γ (Iᵂ.[ x ]) kγ kx)

            q≈ : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≈ G₀Aᴰ.tʰ (r.θ γ)
            q≈ = ≡→≈ q

            x↓ : r.θ x ↓
            x↓ = (q≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂
          p .▷-con-γ γ a [x]≡▷ k▷ = ⊥e (G₀Aᴰ.[[x]]≢cʰ {x* = r.θ x} q)
            where
            kx : Iᵂ.[ Iᵂ.[ x ] ] ≡ Iᵂ.ĉ
            kx = ≡.trans (≡.cong Iᵂ.[_] [x]≡▷) k▷
            q : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.cʰ
            q = ≡.trans (≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ]))
                        (conEq (Iᵂ.[ x ]) kx)
          p .▷-con-a γ a [x]≡▷ k▷ = ⊥e (G₀Aᴰ.[[x]]≢cʰ {x* = r.θ x} q)
            where
            kx : Iᵂ.[ Iᵂ.[ x ] ] ≡ Iᵂ.ĉ
            kx = ≡.trans (≡.cong Iᵂ.[_] [x]≡▷) k▷
            q : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.cʰ
            q = ≡.trans (≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ]))
                        (conEq (Iᵂ.[ x ]) kx)
          p .▷-ty-absurd = {!!}
          p .u-con-absurd = P.u-con-absurd px
          p .u-ty-inv = P.u-ty-inv px

        k̂ : CT
        k̂ = Iᵂ.k̂ , p
          where
          p : P Iᵂ.k̂
          p .Conβ kk̂ = ⊥e (G₀Aᴰ.kʰ≢cʰ k̂≡ĉ)
            where
            k̂≡ĉ : GAᴰ.k̂ ≡ GAᴰ.ĉ
            k̂≡ĉ =
              ≡.trans
                (≡.sym GAᴰ.kk̂)
                (≡.trans (≡.cong GAᴰ.[_] (≡.sym r.k̂))
                          (conEq Iᵂ.k̂ kk̂))
          p .Tyβ γ kγ ka = ⊥e (G₀Aᴰ.[kʰ]≢tʰ {x* = r.θ γ} q)
            where
            q : GAᴰ.[ GAᴰ.k̂ ] ≡ GAᴰ.t̂ (r.θ γ)
            q = ≡.trans (≡.cong GAᴰ.[_] (≡.sym r.k̂))
                          (tyEq γ Iᵂ.k̂ kγ ka)
          p .▷-con-γ γ a x≡▷ k▷ = ⊥e (G₀Aᴰ.[kʰ]≢cʰ {!!})
            where
            q : GAᴰ.[ GAᴰ.k̂ ] ≡ GAᴰ.ĉ
            q = ≡.trans (≡.cong GAᴰ.[_] (≡.sym r.k̂))
                          (conEq Iᵂ.k̂ {!!})
          p .▷-con-a γ a x x₁ = {!!}
          p .▷-ty-absurd = {!!}
          p .u-con-absurd = {!!}
          p .u-ty-inv = {!!}

        kk̂ : [ k̂ ] ≡ k̂
        kk̂ = ΣP≡ _ _ Iᵂ.kk̂

        ĉ : CT
        ĉ = Iᵂ.ĉ , p
          where
          p : P Iᵂ.ĉ
          p .Conβ kĉ = ⊥e (G₀Aᴰ.kʰ≢cʰ k̂≡ĉ)
            where
            k̂≡ĉ : GAᴰ.k̂ ≡ GAᴰ.ĉ
            k̂≡ĉ =
              ≡.trans
                (≡.sym GAᴰ.kĉ)
                (≡.trans (≡.cong GAᴰ.[_] (≡.sym r.ĉ))
                          (conEq Iᵂ.ĉ kĉ))
          p .Tyβ γ kγ ka = ⊥e (G₀Aᴰ.[cʰ]≢tʰ {x* = r.θ γ} q)
            where
            q : GAᴰ.[ GAᴰ.ĉ ] ≡ GAᴰ.t̂ (r.θ γ)
            q = ≡.trans (≡.cong GAᴰ.[_] (≡.sym r.ĉ))
                          (tyEq γ Iᵂ.ĉ kγ ka)
          p .▷-con-γ = {!!}
          p .▷-con-a = {!!}
          p .▷-ty-absurd = {!!}
          p .u-con-absurd = {!!}
          p .u-ty-inv = {!!}

        kĉ : [ ĉ ] ≡ k̂
        kĉ = ΣP≡ _ _ Iᵂ.kĉ

    --     t̂ : CT → CT
    --     t̂ (x , ∧i cx , tx) = Iᵂ.t̂ x , ∧i ct , tyt
    --       where
    --       open ≡.≡-Reasoning
    --       ct : Conβ (Iᵂ.t̂ x)
    --       ct kx = ⊥e (G₀Aᴰ.[tʰ]≢cʰ {x* = r.θ x} p)
    --         where
    --         p : GAᴰ.[ GAᴰ.t̂ (r.θ x) ] ≡ GAᴰ.ĉ
    --         p =
    --           GAᴰ.[ GAᴰ.t̂ (r.θ x) ]
    --             ≡⟨ ≡.cong GAᴰ.[_] (≡.sym (r.t̂ x)) ⟩
    --           GAᴰ.[ r.θ (Iᵂ.t̂ x) ]
    --             ≡⟨ ≡.sym (r.[ Iᵂ.t̂ x ]) ⟩
    --           r.θ Iᵂ.[ Iᵂ.t̂ x ]
    --             ≡⟨ ≡.cong r.θ kx ⟩
    --           r.θ Iᵂ.ĉ
    --             ≡⟨ r.ĉ ⟩
    --           GAᴰ.ĉ ∎
    --       tyt : Tyβ (Iᵂ.t̂ x)
    --       tyt γ kγ ka with tyRet γ (Iᵂ.t̂ x) kγ ka
    --       ... | γ₀ , a₀ , qeq = ⊥e* (G₀Aᴰ.encode (u .snd))
    --         where
    --         p : G₀Aᴰ.tʰ (r.θ x) ≡ return (G₀Aᴰ.ty γ₀ a₀)
    --         p = ≡.trans (≡.sym (r.t̂ x)) (qeq .∧e₁)
    --         u : ΣP G₀Aᴰ.Atom λ z → G₀Aᴰ.t̂ z ≡ G₀Aᴰ.ty γ₀ a₀
    --         u = map-return-inj G₀Aᴰ.t̂ (r.θ x) (G₀Aᴰ.ty γ₀ a₀) p

    --     kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
    --     kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (Iᵂ.kt̂ x (≡.cong fst kγ))

    --     ∙ : CT
    --     ∙ = Iᵂ.∙ , ∧i c∙ , t∙
    --       where
    --       c∙ : Conβ Iᵂ.∙
    --       c∙ k∙ =
    --         r.θ Iᵂ.∙
    --           ≡⟨ r.∙ ⟩
    --         GAᴰ.∙
    --           ≡⟨ ≡.sym (≡.cong fst fᴰ.∙ᴿ) ⟩
    --         fᴰ.conᴿ (Iᵂ.∙ , k∙) .fst ∎
    --         where open ≡.≡-Reasoning
    --       t∙ : Tyβ Iᵂ.∙
    --       t∙ γ kγ ka = ⊥e (G₀Aᴰ.cʰ≢tʰ {x = r.θ γ} p)
    --         where
    --         p : GAᴰ.ĉ ≡ GAᴰ.t̂ (r.θ γ)
    --         p =
    --           ≡.trans
    --             (≡.sym GAᴰ.k∙)
    --             (≡.trans (≡.cong GAᴰ.[_] (≡.sym r.∙))
    --                       (tyEq γ Iᵂ.∙ kγ ka))

    --     k∙ : [ ∙ ] ≡ ĉ
    --     k∙ = ΣP≡ _ _ Iᵂ.k∙

    --     ▷ : CT → CT → CT
    --     ▷ (γ , pγ) (a , pa) =
    --       Iᵂ.▷ γ a , ∧i c▷ , t▷
    --       where
    --       c▷ : Conβ (Iᵂ.▷ γ a)
    --       c▷ kx =
    --         r.θ (Iᵂ.▷ γ a)
    --           ≡⟨ r.▷ γ a kγ ka ⟩
    --         GAᴰ.▷ (r.θ γ) (r.θ a)
    --           ≡⟨ ≡.cong₂ GAᴰ.▷ (pγ .∧e₁ kγ) (pa .∧e₂ γ kγ ka) ⟩
    --         GAᴰ.▷
    --           (fᴰ.conᴿ (γ , kγ) .fst)
    --           (fᴰ.tyᴿ (γ , kγ) (a , ka) .fst)
    --           ≡⟨ ≡.sym (≡.cong fst (fᴰ.▷ᴿ (γ , kγ) (a , ka))) ⟩
    --         fᴰ.conᴿ (Iᵂ.▷ γ a , Iᵂ.k▷ γ a kγ ka) .fst
    --           ≡⟨ p▷ ⟩
    --         fᴰ.conᴿ (Iᵂ.▷ γ a , kx) .fst ∎
    --         where
    --         open ≡.≡-Reasoning
    --         kγa : Iᵂ.[ γ ] ≡ Iᵂ.ĉ ∧ᵖ λ kγ
    --           → Iᵂ.[ a ] ≡ Iᵂ.t̂ γ
    --         kγa = {!▷-con-inv kx!}
    --         kγ = kγa .∧e₁
    --         ka = kγa .∧e₂
    --         p▷ : fᴰ.conᴿ (Iᵂ.▷ γ a , Iᵂ.k▷ γ a kγ ka) .fst
    --            ≡ fᴰ.conᴿ (Iᵂ.▷ γ a , kx) .fst
    --         p▷ = ≡.cong fst (≡.cong fᴰ.conᴿ (ΣP≡ _ _ ≡.refl))
    --       t▷ : Tyβ (Iᵂ.▷ γ a)
    --       t▷ γ kγ ka = ⊥e {!∀ δ → {!▷-ty-absurd γ kγ a {!ka!} δ!}!}

    --     k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
    --     k▷ (γ , pγ) (a , pa) kγ ka = ΣP≡ _ _ (Iᵂ.k▷ γ a (≡.cong fst kγ) (≡.cong fst ka))

    --     u : CT → CT
    --     u (γ , pγ) =
    --       Iᵂ.u γ , ∧i cu , tu
    --       where
    --       cu : Conβ (Iᵂ.u γ)
    --       cu = {!!} 
    --       tu : Tyβ (Iᵂ.u γ)
    --       tu γ kγ ka = {!!}

    --     ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
    --     ku = {!!}

    --     π : CT → CT → CT → CT
    --     π = {!!}

    --     kπ : (γ a b : CT)
    --       → [ γ ] ≡ ĉ
    --       → [ a ] ≡ t̂ γ
    --       → [ b ] ≡ t̂ (▷ γ a)
    --       → [ π γ a b ] ≡ t̂ γ
    --     kπ = {!!}

    --     σ : CT → CT → CT → CT
    --     σ = {!!}

    --     kσ : (γ a b : CT)
    --       → [ γ ] ≡ ĉ
    --       → [ a ] ≡ t̂ γ
    --       → [ b ] ≡ t̂ (▷ γ a)
    --       → [ σ γ a b ] ≡ t̂ γ
    --     kσ = {!!}

    --     σ▷ : (γ a b : CT)
    --       → [ γ ] ≡ ĉ
    --       → [ a ] ≡ t̂ γ
    --       → [ b ] ≡ t̂ (▷ γ a)
    --       → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
    --     σ▷ = {!!}

    --     σπ : (γ a b d : CT)
    --       → [ γ ] ≡ ĉ
    --       → [ a ] ≡ t̂ γ
    --       → [ b ] ≡ t̂ (▷ γ a)
    --       → [ d ] ≡ t̂ (▷ (▷ γ a) b)
    --       → π γ a (π (▷ γ a) b d) ≡ π γ (σ γ a b) d
    --     σπ = {!!}

    --   allP : (x : Iᵂ.CT) → P x
    --   allP x = {!!}

    --   con≡ : (γ : D.Con (F₀ Iᵂ)) → F₁.conᴿ (invFG fᴰ) γ ≡ fᴰ.conᴿ γ
    --   con≡ (γ , kγ) =
    --     ΣP≡ _ _ (allP γ .∧e₁ kγ)

    --   ty≡ : (γ : D.Con (F₀ Iᵂ)) (a : F₀ Iᵂ .D.Ty γ) →
    --          subst (D.Ty (F₀ (G₀ Aᴰ))) (con≡ γ) (D.tyᴿ (F₁ (invFG fᴰ)) γ a) ≡
    --          fᴰ.tyᴿ γ a
    --   ty≡ (γ , kγ) (a , ka) = {!!}

    -- --     [_] : CT → CT
    -- --     [ x , ∧i cx , cy ] = Iᵂ.[ x ] , ∧i c[x] , t[x]
    -- --       where
    -- --       c[x] : Conβ Iᵂ.[ x ]
    -- --       c[x] kx = ⊥e (G₀Aᴰ.[[x]]≢cʰ {x* = r.θ x} p)
    -- --         where
    -- --         p : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.cʰ
    -- --         p = ≡.trans (≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ])) (conEq (Iᵂ.[ x ]) kx)
    -- --       t[x] : Tyβ Iᵂ.[ x ]
    -- --       t[x] γ kγ ka =
    -- --         ⊥e (G₀Aᴰ.[[x]]≢tʰ
    -- --           {x* = r.θ x}
    -- --           {y* = r.θ γ}
    -- --           x↓
    -- --           p)
    -- --         where
    -- --         γ↓ : r.θ γ ↓
    -- --         γ↓ = conDef γ kγ

    -- --         p : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.tʰ (r.θ γ)
    -- --         p = ≡.trans (≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ])) (tyEq γ (Iᵂ.[ x ]) kγ ka)

    -- --         p≈ : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≈ G₀Aᴰ.tʰ (r.θ γ)
    -- --         p≈ = ≡→≈ p

    -- --         x↓ : r.θ x ↓
    -- --         x↓ = (p≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂

    -- --     k̂ : CT
    -- --     k̂ = Iᵂ.k̂ , ∧i ck̂ , tk̂
    -- --       where
    -- --       ck̂ : Conβ Fr.A.k̂
    -- --       ck̂ kk̂ = ⊥e (G₀Aᴰ.kʰ≢cʰ k̂≡ĉ)
    -- --         where
    -- --         k̂≡ĉ : GAᴰ.k̂ ≡ GAᴰ.ĉ
    -- --         k̂≡ĉ =
    -- --           ≡.trans
    -- --             (≡.sym GAᴰ.kk̂)
    -- --             (≡.trans (≡.cong GAᴰ.[_] (≡.sym r.k̂))
    -- --                       (conEq Iᵂ.k̂ kk̂))
    -- --       tk̂ : Tyβ Fr.A.k̂
    -- --       tk̂ γ kγ ka = ⊥e (G₀Aᴰ.[kʰ]≢tʰ {x* = r.θ γ} p)
    -- --         where
    -- --         p : GAᴰ.[ GAᴰ.k̂ ] ≡ GAᴰ.t̂ (r.θ γ)
    -- --         p = ≡.trans (≡.cong GAᴰ.[_] (≡.sym r.k̂)) (tyEq γ Iᵂ.k̂ kγ ka)

    -- --     kk̂ : [ k̂ ] ≡ k̂
    -- --     kk̂ = ΣP≡ _ _ Iᵂ.kk̂

    -- --     ĉ : CT
    -- --     ĉ = Iᵂ.ĉ , ∧i cĉ , tĉ
    -- --       where
    -- --       cĉ : Conβ Iᵂ.ĉ
    -- --       cĉ kĉ = ⊥e (G₀Aᴰ.kʰ≢cʰ k̂≡ĉ)
    -- --         where
    -- --         k̂≡ĉ : GAᴰ.k̂ ≡ GAᴰ.ĉ
    -- --         k̂≡ĉ =
    -- --           ≡.trans
    -- --             (≡.sym GAᴰ.kĉ)
    -- --             (≡.trans (≡.cong GAᴰ.[_] (≡.sym r.ĉ))
    -- --                       (conEq Iᵂ.ĉ kĉ))
    -- --       tĉ : Tyβ Iᵂ.ĉ
    -- --       tĉ γ kγ ka = ⊥e (G₀Aᴰ.[cʰ]≢tʰ {x* = r.θ γ} p)
    -- --         where
    -- --         p : GAᴰ.[ GAᴰ.ĉ ] ≡ GAᴰ.t̂ (r.θ γ)
    -- --         p = ≡.trans (≡.cong GAᴰ.[_] (≡.sym r.ĉ)) (tyEq γ Iᵂ.ĉ kγ ka)

    -- --     kĉ : [ ĉ ] ≡ k̂
    -- --     kĉ = ΣP≡ _ _ Iᵂ.kĉ

    -- --     t̂ : CT → CT
    -- --     t̂ (x , ∧i cx , tx) = Iᵂ.t̂ x , ∧i ct , tyt
    -- --       where
    -- --       open ≡.≡-Reasoning
    -- --       ct : Conβ (Iᵂ.t̂ x)
    -- --       ct kx = ⊥e (G₀Aᴰ.[tʰ]≢cʰ {x* = r.θ x} p)
    -- --         where
    -- --         p : GAᴰ.[ GAᴰ.t̂ (r.θ x) ] ≡ GAᴰ.ĉ
    -- --         p =
    -- --           GAᴰ.[ GAᴰ.t̂ (r.θ x) ]
    -- --             ≡⟨ ≡.cong GAᴰ.[_] (≡.sym (r.t̂ x)) ⟩
    -- --           GAᴰ.[ r.θ (Iᵂ.t̂ x) ]
    -- --             ≡⟨ ≡.sym (r.[ Iᵂ.t̂ x ]) ⟩
    -- --           r.θ Iᵂ.[ Iᵂ.t̂ x ]
    -- --             ≡⟨ ≡.cong r.θ kx ⟩
    -- --           r.θ Iᵂ.ĉ
    -- --             ≡⟨ r.ĉ ⟩
    -- --           GAᴰ.ĉ ∎
    -- --       tyt : Tyβ (Iᵂ.t̂ x)
    -- --       tyt γ kγ ka with tyRet γ (Iᵂ.t̂ x) kγ ka
    -- --       ... | γ₀ , a₀ , qeq = ⊥e* (G₀Aᴰ.encode (u .snd))
    -- --         where
    -- --         p : G₀Aᴰ.tʰ (r.θ x) ≡ return (G₀Aᴰ.ty γ₀ a₀)
    -- --         p = ≡.trans (≡.sym (r.t̂ x)) (qeq .∧e₁)
    -- --         u : ΣP G₀Aᴰ.Atom λ z → G₀Aᴰ.t̂ z ≡ G₀Aᴰ.ty γ₀ a₀
    -- --         u = map-return-inj G₀Aᴰ.t̂ (r.θ x) (G₀Aᴰ.ty γ₀ a₀) p

    -- --     kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
    -- --     kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (Iᵂ.kt̂ x (≡.cong fst kγ))

    -- --     ∙ : CT
    -- --     ∙ = Iᵂ.∙ , ∧i c∙ , t∙
    -- --       where
    -- --       c∙ : Conβ Iᵂ.∙
    -- --       c∙ k∙ =
    -- --         r.θ Iᵂ.∙
    -- --           ≡⟨ r.∙ ⟩
    -- --         GAᴰ.∙
    -- --           ≡⟨ ≡.sym (≡.cong fst fᴰ.∙ᴿ) ⟩
    -- --         fᴰ.conᴿ (Iᵂ.∙ , k∙) .fst ∎
    -- --         where open ≡.≡-Reasoning
    -- --       t∙ : Tyβ Iᵂ.∙
    -- --       t∙ γ kγ ka = ⊥e (G₀Aᴰ.cʰ≢tʰ {x = r.θ γ} p)
    -- --         where
    -- --         p : GAᴰ.ĉ ≡ GAᴰ.t̂ (r.θ γ)
    -- --         p =
    -- --           ≡.trans
    -- --             (≡.sym GAᴰ.k∙)
    -- --             (≡.trans (≡.cong GAᴰ.[_] (≡.sym r.∙))
    -- --                       (tyEq γ Iᵂ.∙ kγ ka))

    -- --     k∙ : [ ∙ ] ≡ ĉ
    -- --     k∙ = ΣP≡ _ _ Iᵂ.k∙

    -- --     ▷ : CT → CT → CT
    -- --     ▷ (γ , pγ) (a , pa) =
    -- --       Iᵂ.▷ γ a , ∧i c▷ , t▷
    -- --       where
    -- --       c▷ : Conβ (Iᵂ.▷ γ a)
    -- --       c▷ kx =
    -- --         r.θ (Iᵂ.▷ γ a)
    -- --           ≡⟨ r.▷ γ a kγ ka ⟩
    -- --         GAᴰ.▷ (r.θ γ) (r.θ a)
    -- --           ≡⟨ ≡.cong₂ GAᴰ.▷ (pγ .∧e₁ kγ) (pa .∧e₂ γ kγ ka) ⟩
    -- --         GAᴰ.▷
    -- --           (fᴰ.conᴿ (γ , kγ) .fst)
    -- --           (fᴰ.tyᴿ (γ , kγ) (a , ka) .fst)
    -- --           ≡⟨ ≡.sym (≡.cong fst (fᴰ.▷ᴿ (γ , kγ) (a , ka))) ⟩
    -- --         fᴰ.conᴿ (Iᵂ.▷ γ a , Iᵂ.k▷ γ a kγ ka) .fst
    -- --           ≡⟨ p▷ ⟩
    -- --         fᴰ.conᴿ (Iᵂ.▷ γ a , kx) .fst ∎
    -- --         where
    -- --         open ≡.≡-Reasoning
    -- --         kγa : Iᵂ.[ γ ] ≡ Iᵂ.ĉ ∧ᵖ λ kγ
    -- --           → Iᵂ.[ a ] ≡ Iᵂ.t̂ γ
    -- --         kγa = ▷-con-inv kx
    -- --         kγ = kγa .∧e₁
    -- --         ka = kγa .∧e₂
    -- --         p▷ : fᴰ.conᴿ (Iᵂ.▷ γ a , Iᵂ.k▷ γ a kγ ka) .fst
    -- --            ≡ fᴰ.conᴿ (Iᵂ.▷ γ a , kx) .fst
    -- --         p▷ = ≡.cong fst (≡.cong fᴰ.conᴿ (ΣP≡ _ _ ≡.refl))
    -- --       t▷ : Tyβ (Iᵂ.▷ γ a)
    -- --       t▷ γ kγ ka = ⊥e {!∀ δ → {!▷-ty-absurd γ kγ a {!ka!} δ!}!}

    -- --     k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
    -- --     k▷ (γ , pγ) (a , pa) kγ ka = ΣP≡ _ _ (Iᵂ.k▷ γ a (≡.cong fst kγ) (≡.cong fst ka))

    -- --     u : CT → CT
    -- --     u (γ , pγ) =
    -- --       Iᵂ.u γ , ∧i cu , tu
    -- --       where
    -- --       cu : Conβ (Iᵂ.u γ)
    -- --       cu = {!!} 
    -- --       tu : Tyβ (Iᵂ.u γ)
    -- --       tu γ kγ ka = {!!}

    -- --     ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
    -- --     ku = {!!}

    -- --     π : CT → CT → CT → CT
    -- --     π = {!!}

    -- --     kπ : (γ a b : CT)
    -- --       → [ γ ] ≡ ĉ
    -- --       → [ a ] ≡ t̂ γ
    -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- --       → [ π γ a b ] ≡ t̂ γ
    -- --     kπ = {!!}

    -- --     σ : CT → CT → CT → CT
    -- --     σ = {!!}

    -- --     kσ : (γ a b : CT)
    -- --       → [ γ ] ≡ ĉ
    -- --       → [ a ] ≡ t̂ γ
    -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- --       → [ σ γ a b ] ≡ t̂ γ
    -- --     kσ = {!!}

    -- --     σ▷ : (γ a b : CT)
    -- --       → [ γ ] ≡ ĉ
    -- --       → [ a ] ≡ t̂ γ
    -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- --       → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
    -- --     σ▷ = {!!}

    -- --     σπ : (γ a b d : CT)
    -- --       → [ γ ] ≡ ĉ
    -- --       → [ a ] ≡ t̂ γ
    -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- --       → [ d ] ≡ t̂ (▷ (▷ γ a) b)
    -- --       → π γ a (π (▷ γ a) b d) ≡ π γ (σ γ a b) d
    -- --     σπ = {!!}

    -- --   allP : (x : Iᵂ.CT) → P x
    -- --   allP x = {!!}

    -- --   con≡ : (γ : D.Con (F₀ Iᵂ)) → F₁.conᴿ (invFG fᴰ) γ ≡ fᴰ.conᴿ γ
    -- --   con≡ (γ , kγ) =
    -- --     ΣP≡ _ _ (allP γ .∧e₁ kγ)

    -- --   ty≡ : (γ : D.Con (F₀ Iᵂ)) (a : F₀ Iᵂ .D.Ty γ) →
    -- --          subst (D.Ty (F₀ (G₀ Aᴰ))) (con≡ γ) (D.tyᴿ (F₁ (invFG fᴰ)) γ a) ≡
    -- --          fᴰ.tyᴿ γ a
    -- --   ty≡ (γ , kγ) (a , ka) = {!!}

    -- -- recUniqueᴰ : {Aᴰ : D.Algebra ℓA} → (fᴰ : D.Hom Iᴰ Aᴰ) → fᴰ D.≈ recᴰ Aᴰ
    -- -- recUniqueᴰ {Aᴰ = Aᴰ} fᴰ = D≈.trans Iᴰ Aᴰ (D≈.sym (F₀ Iᵂ) Aᴰ β) η
    -- --   where
    -- --   module D≈ {ℓA} {ℓB} A B = ≈.Setoid (D.HomSetoid {ℓA} {ℓB} A B)
    -- --   module Dᶜ ℓA = Category (D.Cat ℓA)
    -- --   module F ℓA = Functor (F ℓA)
    -- --   q : D.Hom Iᴰ (F₀ (G₀ Aᴰ))
    -- --   q = ε⁻ Aᴰ D.∘ fᴰ
    -- --   β : (ε Aᴰ D.∘ F₁ (invFG q)) D.≈ fᴰ
    -- --   β =
    -- --     ε Aᴰ D.∘ F₁ (invFG q)
    -- --       ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ Aᴰ)) Aᴰ {ε Aᴰ}) (invFG-beta q) ⟩
    -- --     ε Aᴰ D.∘ (ε⁻ Aᴰ D.∘ fᴰ)
    -- --       ≈⟨ D≈.refl Iᴰ Aᴰ ⟩
    -- --     fᴰ ∎
    -- --     where
    -- --     open ≈.≈syntax {S = D.HomSetoid Iᴰ Aᴰ}
    -- --   η : (ε Aᴰ D.∘ F₁ (invFG q)) D.≈ recᴰ Aᴰ
    -- --   η =
    -- --     ε Aᴰ D.∘ F₁ (invFG q)
    -- --       ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ Aᴰ)) Aᴰ {ε Aᴰ})
    -- --                     (F.resp (lsuc ℓA) (recUniqueᵂ (invFG q))) ⟩
    -- --     ε Aᴰ D.∘ F₁ (recᵂ (G₀ Aᴰ)) ∎
    -- --     where
    -- --     open ≈.≈syntax {S = D.HomSetoid Iᴰ Aᴰ}
