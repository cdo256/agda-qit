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
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Category.Base
open import QIT.Functor.NatTrans 
open import QIT.Functor.Properties

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
  conAtom (γ , kγ) = γ .proj₂ (G.conData₁ γ kγ)

  conAtom-isCon : (γ : DFA.Con) → G.[ conAtom γ ]₀ ≡ G.ĉ
  conAtom-isCon (γ , kγ) = G.conData₂ γ kγ

  conᴿ : DFA.Con → DA.Con
  conᴿ γ = G.Con₀ (conAtom γ) (conAtom-isCon γ)

  tyAtom : (γ : DFA.Con) → DFA.Ty γ → G.Atom
  tyAtom (γ , kγ) (a , ka) = a .proj₂ (G.tyData₁ γ a kγ ka)

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
  ι x = ⊤* , λ _ → x

  kcon : (γ : DA.Con) → G.[ ι (G.con γ) ] ≡ G.cʰ
  kcon γ = G.mkCT≡ (λ _ → tt*) (λ _ → ∧i tt* , tt*) λ _ _ → ≡.refl

  kty : (γ : DA.Con) (a : DA.Ty γ) → G.[ ι (G.ty γ a) ] ≡ G.tʰ (ι (G.con γ))
  kty γ a = G.mkCT≡ (λ p → p) (λ p → p) λ _ _ → ≡.refl

  ▷ι : (γ : DA.Con) (a : DA.Ty γ) → G.▷ (ι (G.con γ)) (ι (G.ty γ a)) ≡ ι (G.con (γ DA.▷ a))
  ▷ι γ a = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → proj₁ (G.▷ (ι (G.con γ)) (ι (G.ty γ a)))
    q _ = ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , tt*

  uι : (γ : DA.Con) → G.u (ι (G.con γ)) ≡ ι (G.ty γ (DA.u γ))
  uι γ = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → proj₁ (G.u (ι (G.con γ)))
    q _ = ∧i tt* , ∧i ≡.refl , tt*

  πι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.π γ a b))
  πι γ a b = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → proj₁ (G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)))
    q _ = ∧i tt* , ∧i tt* , ∧i tt* , ∧i ≡.refl , ∧i ≡.refl , ∧i ≡.refl , tt*

  σι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.σ γ a b))
  σι γ a b = G.mkCT≡ (λ _ → tt*) q λ _ _ → ≡.refl
    where
    q : LiftP ℓA ⊤ → proj₁ (G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)))
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

  inhabited→ι : (x : G.CT) → (p : x .proj₁) → x ≡ ι (x .proj₂ p)
  inhabited→ι (P , f) p = G.mkCT≡ (λ _ → tt*) (λ _ → p) (λ q _ → ≡.congp f)

  Ty₀-η : (γ a : G.Atom)
    → (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → (ka : G.[ a ]₀ ≡ G.t̂ γ)
    → G.ty (G.Con₀ γ kγ) (G.Ty₀ γ a kγ ka) ≡ a
  Ty₀-η (G.con γ) (G.ty .γ a) ≡.refl ≡.refl = ≡.refl

  con≡ : (γ : DFA.Con) → (ε⁻ A D.∘ ε A) .D.conᴿ γ ≡ D.conᴿ (D.id {A = F₀ (G₀ A)}) γ
  con≡ γ@(x , kx) = ΣP≡ _ _ p
    where
    witness : x .proj₁
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
    witness : y .proj₁
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
  (Iᵂ : W.Algebra ℓA)
  (recᵂ : (Aᵂ : W.Algebra ℓA) → W.Hom Iᵂ Aᵂ)
  (recUniqueᵂ : {Aᵂ : W.Algebra ℓA} → (f : W.Hom Iᵂ Aᵂ) → f W.≈ recᵂ Aᵂ)
  where

  Iᴰ : D.Algebra ℓA
  Iᴰ = F₀ Iᵂ
  recᴰ : (Aᴰ : D.Algebra ℓA) → D.Hom Iᴰ Aᴰ
  recᴰ Aᴰ = ε Aᴰ D.∘ {!F₁ ?!}
