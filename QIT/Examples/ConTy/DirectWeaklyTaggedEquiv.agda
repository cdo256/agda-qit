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
  kcon γ = G.mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , tt*) λ _ _ → ≡.refl

  kty : (γ : DA.Con) (a : DA.Ty γ) → G.[ ι (G.ty γ a) ] ≡ G.tʰ (ι (G.con γ))
  kty γ a = G.mkCT≡ (λ p → p) (λ p → p) λ _ _ → ≡.refl

  ▷ι : (γ : DA.Con) (a : DA.Ty γ) → G.▷ (ι (G.con γ)) (ι (G.ty γ a)) ≡ ι (G.con (γ DA.▷ a))
  ▷ι γ a = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → G.▷ (ι (G.con γ)) (ι (G.ty γ a)) .Cond
    q _ = ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , tt*

  uι : (γ : DA.Con) → G.u (ι (G.con γ)) ≡ ι (G.ty γ (DA.u γ))
  uι γ = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → G.u (ι (G.con γ)) .Cond
    q _ = ∧i tt* , ∧i ≡.refl , tt*

  πι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.π γ a b))
  πι γ a b = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) .Cond
    q _ = ∧i tt* , ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , ∧i ≡.refl , tt*

  σι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.σ γ a b))
  σι γ a b = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) .Cond
    q _ = ∧i tt* , ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , ∧i ≡.refl , tt*

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

  invFG : {Aᴰ : D.Algebra ℓA} → D.Hom {ℓA = lsuc ℓA} (F₀ Iᵂ) (F₀ (G₀ Aᴰ))
         → W.Hom {ℓA = lsuc ℓA} Iᵂ (G₀ Aᴰ)
  invFG {Aᴰ = Aᴰ} fᴰ = recᵂ (G₀ Aᴰ)
      
  invFG-beta : {Aᴰ : D.Algebra ℓA}
          → (fᴰ : D.Hom (F₀ Iᵂ) (F₀ (G₀ Aᴰ)))
          → F₁ (invFG fᴰ) D.≈ fᴰ
  invFG-beta {Aᴰ = Aᴰ} fᴰ =
    D.mk≈ con≡ ty≡
    where
    module fᴰ = D.Hom fᴰ
    module Aᴰ = D.Algebra Aᴰ
    r : W.Hom Iᵂ (G₀ Aᴰ)
    r = invFG fᴰ

    module G₀Aᴰ = G₀ Aᴰ
    module GAᴰ = W.Algebra (G₀ Aᴰ)
    module r = W.Hom r
    module Fr = F₁ r

    Conβ : Iᵂ.CT → Prop _
    Conβ x =
      (kx : Iᵂ.[ x ] ≡ Iᵂ.ĉ)
      → r.θ x ≡ fᴰ.conᴿ (x , kx) .fst

    Tyβ : Iᵂ.CT → Prop _
    Tyβ a =
      (γ : Iᵂ.CT)
      → (kγ : Iᵂ.[ γ ] ≡ Iᵂ.ĉ)
      → (ka : Iᵂ.[ a ] ≡ Iᵂ.t̂ γ)
      → r.θ a ≡ fᴰ.tyᴿ (γ , kγ) (a , ka) .fst

    P : Iᵂ.CT → Prop _
    P x = Conβ x ∧ᵖ λ _ → Tyβ x

    Pᵂ : W.Algebra (lsuc ℓA)
    Pᵂ = record
      { CT = CT
      ; [_] = [_]
      ; k̂ = k̂
      ; kk̂ = kk̂
      ; ĉ = ĉ
      ; kĉ = kĉ
      ; t̂ = t̂
      ; kt̂ = kt̂
      ; ∙ = ∙
      ; k∙ = k∙
      ; ▷ = ▷
      ; k▷ = k▷
      ; u = u
      ; ku = ku
      ; π = π
      ; kπ = kπ
      ; σ = σ
      ; kσ = kσ
      ; σ▷ = σ▷
      ; σπ = σπ
      }
      where
      CT : Set (lsuc ℓA)
      CT = ΣP Iᵂ.CT P

      [_] : CT → CT
      [ x , ∧i cx , cy ] = Iᵂ.[ x ] , ∧i c[x] , t[x]
        where
        open ≡.≡-Reasoning
        c[x] : Conβ Iᵂ.[ x ]
        c[x] kx = ⊥e (G₀Aᴰ.[[x]]≢cʰ {x* = r.θ x} p)
          where
          p : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.cʰ
          p =
            G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ]
              ≡⟨ ≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ]) ⟩
            G₀Aᴰ.[ r.θ Iᵂ.[ x ] ]
              ≡⟨ ≡.sym r.[ Fr.A.[ x ] ] ⟩
            r.θ Iᵂ.[ Iᵂ.[ x ] ]
              ≡⟨ ≡.cong r.θ kx ⟩
            r.θ Iᵂ.ĉ
              ≡⟨ r.ĉ ⟩
            G₀Aᴰ.cʰ ∎
        t[x] : Tyβ Iᵂ.[ x ]
        t[x] γ kγ ka =
          ⊥e (G₀Aᴰ.[[x]]≢tʰ
            {x* = r.θ x}
            {y* = r.θ γ}
            x↓
            p)
          where
          γ-eq : G₀Aᴰ.[ r.θ γ ] ≡ G₀Aᴰ.cʰ
          γ-eq =
            G₀Aᴰ.[ r.θ γ ]
              ≡⟨ ≡.sym r.[ γ ] ⟩
            r.θ Iᵂ.[ γ ]
              ≡⟨ ≡.cong r.θ kγ ⟩
            r.θ Iᵂ.ĉ
              ≡⟨ r.ĉ ⟩
            G₀Aᴰ.cʰ ∎

          γ-eq≈ : G₀Aᴰ.[ r.θ γ ] ≈ G₀Aᴰ.cʰ
          γ-eq≈ = ≡→≈ γ-eq

          γ↓ : r.θ γ ↓
          γ↓ =
            γ-eq≈ .∧e₁ .∧e₂ tt* .∧e₂

          p : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ] ≡ G₀Aᴰ.tʰ (r.θ γ)
          p =
            G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ]
              ≡⟨ ≡.cong G₀Aᴰ.[_] (≡.sym r.[ x ]) ⟩
            G₀Aᴰ.[ r.θ Iᵂ.[ x ] ]
              ≡⟨ ≡.sym r.[ Fr.A.[ x ] ] ⟩
            r.θ Iᵂ.[ Iᵂ.[ x ] ]
              ≡⟨ ≡.cong r.θ ka ⟩
            r.θ (Iᵂ.t̂ γ)
              ≡⟨ r.t̂ γ ⟩
            G₀Aᴰ.tʰ (r.θ γ) ∎

          p≈ : G₀Aᴰ.[ G₀Aᴰ.[ r.θ x ] ]
              ≈ G₀Aᴰ.tʰ (r.θ γ)
          p≈ = ≡→≈ p

          x↓ : r.θ x ↓
          x↓ = (p≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂

      k̂ : CT
      k̂ = Iᵂ.k̂ , ∧i ck̂ , tk̂
        where
        open ≡.≡-Reasoning
        ck̂ : Conβ Fr.A.k̂
        ck̂ kk̂ = ⊥e (G₀Aᴰ.kʰ≢cʰ k̂≡ĉ)
          where
          k̂≡ĉ : GAᴰ.k̂ ≡ GAᴰ.ĉ
          k̂≡ĉ =
            GAᴰ.k̂
              ≡⟨ ≡.sym GAᴰ.kk̂ ⟩
            GAᴰ.[ GAᴰ.k̂ ]
              ≡⟨ ≡.cong GAᴰ.[_] (≡.sym r.k̂) ⟩
            GAᴰ.[ r.θ Iᵂ.k̂ ]
              ≡⟨ ≡.sym (r.[ Iᵂ.k̂ ]) ⟩
            r.θ Iᵂ.[ Iᵂ.k̂ ]
              ≡⟨ ≡.cong r.θ kk̂ ⟩
            r.θ Iᵂ.ĉ
              ≡⟨ r.ĉ ⟩
            GAᴰ.ĉ ∎
        tk̂ : Tyβ Fr.A.k̂
        tk̂ γ kγ ka = ⊥e (G₀Aᴰ.[kʰ]≢tʰ {x* = r.θ γ} p)
          where
          p : GAᴰ.[ GAᴰ.k̂ ] ≡ GAᴰ.t̂ (r.θ γ)
          p =
            GAᴰ.[ GAᴰ.k̂ ]
              ≡⟨ ≡.cong GAᴰ.[_] (≡.sym r.k̂) ⟩
            GAᴰ.[ r.θ Iᵂ.k̂ ]
              ≡⟨ ≡.sym (r.[ Iᵂ.k̂ ]) ⟩
            r.θ Iᵂ.[ Iᵂ.k̂ ]
              ≡⟨ ≡.cong r.θ ka ⟩
            r.θ (Iᵂ.t̂ γ)
              ≡⟨ r.t̂ γ ⟩
            GAᴰ.t̂ (r.θ γ) ∎

      kk̂ : [ k̂ ] ≡ k̂
      kk̂ = ΣP≡ _ _ Iᵂ.kk̂

      ĉ : CT
      ĉ = Iᵂ.ĉ , ∧i cĉ , tĉ
        where
        open ≡.≡-Reasoning
        cĉ : Conβ Iᵂ.ĉ
        cĉ kĉ = ⊥e (G₀Aᴰ.kʰ≢cʰ k̂≡ĉ)
          where
          k̂≡ĉ : GAᴰ.k̂ ≡ GAᴰ.ĉ
          k̂≡ĉ =
            GAᴰ.k̂
              ≡⟨ ≡.sym GAᴰ.kĉ ⟩
            GAᴰ.[ GAᴰ.ĉ ]
              ≡⟨ ≡.cong GAᴰ.[_] (≡.sym r.ĉ) ⟩
            GAᴰ.[ r.θ Iᵂ.ĉ ]
              ≡⟨ ≡.sym (r.[ Iᵂ.ĉ ]) ⟩
            r.θ Iᵂ.[ Iᵂ.ĉ ]
              ≡⟨ ≡.cong r.θ kĉ ⟩
            r.θ Iᵂ.ĉ
              ≡⟨ r.ĉ ⟩
            GAᴰ.ĉ ∎
        tĉ : Tyβ Iᵂ.ĉ
        tĉ γ kγ ka = ⊥e (G₀Aᴰ.[cʰ]≢tʰ {x* = r.θ γ} p)
          where
          p : GAᴰ.[ GAᴰ.ĉ ] ≡ GAᴰ.t̂ (r.θ γ)
          p =
            GAᴰ.[ GAᴰ.ĉ ]
              ≡⟨ ≡.cong GAᴰ.[_] (≡.sym r.ĉ) ⟩
            GAᴰ.[ r.θ Iᵂ.ĉ ]
              ≡⟨ ≡.sym (r.[ Iᵂ.ĉ ]) ⟩
            r.θ Iᵂ.[ Iᵂ.ĉ ]
              ≡⟨ ≡.cong r.θ ka ⟩
            r.θ (Iᵂ.t̂ γ)
              ≡⟨ r.t̂ γ ⟩
            GAᴰ.t̂ (r.θ γ) ∎

      kĉ : [ ĉ ] ≡ k̂
      kĉ = ΣP≡ _ _ Iᵂ.kĉ

      t̂ : CT → CT
      t̂ (x , ∧i cx , tx) = Iᵂ.t̂ x , ∧i ct , tyt
        where
        open ≡.≡-Reasoning
        ct : Conβ (Iᵂ.t̂ x)
        ct kx = ⊥e (G₀Aᴰ.[tʰ]≢cʰ {x* = r.θ x} p)
          where
          p : GAᴰ.[ GAᴰ.t̂ (r.θ x) ] ≡ GAᴰ.ĉ
          p =
            GAᴰ.[ GAᴰ.t̂ (r.θ x) ]
              ≡⟨ ≡.cong GAᴰ.[_] (≡.sym (r.t̂ x)) ⟩
            GAᴰ.[ r.θ (Iᵂ.t̂ x) ]
              ≡⟨ ≡.sym (r.[ Iᵂ.t̂ x ]) ⟩
            r.θ Iᵂ.[ Iᵂ.t̂ x ]
              ≡⟨ ≡.cong r.θ kx ⟩
            r.θ Iᵂ.ĉ
              ≡⟨ r.ĉ ⟩
            GAᴰ.ĉ ∎
        tyt : Tyβ (Iᵂ.t̂ x)
        tyt = {!!}

      kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
      kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (Iᵂ.kt̂ x (≡.cong fst kγ))

      ∙ : CT
      ∙ = Iᵂ.∙ , ∧i c∙ , t∙
        where
        open ≡.≡-Reasoning
        c∙ : Conβ Iᵂ.∙
        c∙ k∙ =
          r.θ Iᵂ.∙
            ≡⟨ r.∙ ⟩
          GAᴰ.∙
            ≡⟨ ≡.sym (≡.cong fst fᴰ.∙ᴿ) ⟩
          fᴰ.conᴿ (Iᵂ.∙ , k∙) .fst ∎
        t∙ : Tyβ Iᵂ.∙
        t∙ γ kγ ka = ⊥e (G₀Aᴰ.cʰ≢tʰ {x = r.θ γ} p)
          where
          p : GAᴰ.ĉ ≡ GAᴰ.t̂ (r.θ γ)
          p =
            GAᴰ.ĉ
              ≡⟨ ≡.sym GAᴰ.k∙ ⟩
            GAᴰ.[ GAᴰ.∙ ]
              ≡⟨ ≡.cong GAᴰ.[_] (≡.sym r.∙) ⟩
            GAᴰ.[ r.θ Iᵂ.∙ ]
              ≡⟨ ≡.sym (r.[ Iᵂ.∙ ]) ⟩
            r.θ Iᵂ.[ Iᵂ.∙ ]
              ≡⟨ ≡.cong r.θ ka ⟩
            r.θ (Iᵂ.t̂ γ)
              ≡⟨ r.t̂ γ ⟩
            GAᴰ.t̂ (r.θ γ) ∎

      k∙ : [ ∙ ] ≡ ĉ
      k∙ = ΣP≡ _ _ Iᵂ.k∙

      ▷ : CT → CT → CT
      ▷ (γ , pγ) (a , pa) =
        Iᵂ.▷ γ a , ∧i c▷ , t▷
        where
        c▷ : Conβ (Fr.A.▷ γ a)
        c▷ = {!!}
        t▷ : Tyβ (Fr.A.▷ γ a)
        t▷ γ kγ ka = ⊥e {!!}

      k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
      k▷ = {!!}

      u : CT → CT
      u = {!!}

      ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
      ku = {!!}

      π : CT → CT → CT → CT
      π = {!!}

      kπ : (γ a b : CT)
        → [ γ ] ≡ ĉ
        → [ a ] ≡ t̂ γ
        → [ b ] ≡ t̂ (▷ γ a)
        → [ π γ a b ] ≡ t̂ γ
      kπ = {!!}

      σ : CT → CT → CT → CT
      σ = {!!}

      kσ : (γ a b : CT)
        → [ γ ] ≡ ĉ
        → [ a ] ≡ t̂ γ
        → [ b ] ≡ t̂ (▷ γ a)
        → [ σ γ a b ] ≡ t̂ γ
      kσ = {!!}

      σ▷ : (γ a b : CT)
        → [ γ ] ≡ ĉ
        → [ a ] ≡ t̂ γ
        → [ b ] ≡ t̂ (▷ γ a)
        → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
      σ▷ = {!!}

      σπ : (γ a b d : CT)
        → [ γ ] ≡ ĉ
        → [ a ] ≡ t̂ γ
        → [ b ] ≡ t̂ (▷ γ a)
        → [ d ] ≡ t̂ (▷ (▷ γ a) b)
        → π γ a (π (▷ γ a) b d) ≡ π γ (σ γ a b) d
      σπ = {!!}

    allP : (x : Iᵂ.CT) → P x
    allP x = {!!}

    con≡ : (γ : D.Con (F₀ Iᵂ)) → F₁.conᴿ (invFG fᴰ) γ ≡ fᴰ.conᴿ γ
    con≡ (γ , kγ) =
      ΣP≡ _ _ (allP γ .∧e₁ kγ)

    ty≡ : (γ : D.Con (F₀ Iᵂ)) (a : F₀ Iᵂ .D.Ty γ) →
           subst (D.Ty (F₀ (G₀ Aᴰ))) (con≡ γ) (D.tyᴿ (F₁ (invFG fᴰ)) γ a) ≡
           fᴰ.tyᴿ γ a
    ty≡ (γ , kγ) (a , ka) = {!!}

  recUniqueᴰ : {Aᴰ : D.Algebra ℓA} → (fᴰ : D.Hom Iᴰ Aᴰ) → fᴰ D.≈ recᴰ Aᴰ
  recUniqueᴰ {Aᴰ = Aᴰ} fᴰ = D≈.trans Iᴰ Aᴰ (D≈.sym (F₀ Iᵂ) Aᴰ β) η
    where
    module D≈ {ℓA} {ℓB} A B = ≈.Setoid (D.HomSetoid {ℓA} {ℓB} A B)
    module Dᶜ ℓA = Category (D.Cat ℓA)
    module F ℓA = Functor (F ℓA)
    q : D.Hom Iᴰ (F₀ (G₀ Aᴰ))
    q = ε⁻ Aᴰ D.∘ fᴰ
    β : (ε Aᴰ D.∘ F₁ (invFG q)) D.≈ fᴰ
    β =
      ε Aᴰ D.∘ F₁ (invFG q)
        ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ Aᴰ)) Aᴰ {ε Aᴰ}) (invFG-beta q) ⟩
      ε Aᴰ D.∘ (ε⁻ Aᴰ D.∘ fᴰ)
        ≈⟨ D≈.refl Iᴰ Aᴰ ⟩
      fᴰ ∎
      where
      open ≈.≈syntax {S = D.HomSetoid Iᴰ Aᴰ}
    η : (ε Aᴰ D.∘ F₁ (invFG q)) D.≈ recᴰ Aᴰ
    η =
      ε Aᴰ D.∘ F₁ (invFG q)
        ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ Aᴰ)) Aᴰ {ε Aᴰ})
                      (F.resp (lsuc ℓA) (recUniqueᵂ (invFG q))) ⟩
      ε Aᴰ D.∘ F₁ (recᵂ (G₀ Aᴰ)) ∎
      where
      open ≈.≈syntax {S = D.HomSetoid Iᴰ Aᴰ}
