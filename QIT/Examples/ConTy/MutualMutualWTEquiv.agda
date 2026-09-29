{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.Examples.ConTy.MutualMutualWTEquiv
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

import QIT.Examples.ConTy.MutualProjection as D
import QIT.Examples.ConTy.MutualWeaklyTagged as W

open import QIT.Examples.ConTy.MutualToMutualWT
open import QIT.Examples.ConTy.MutualWTToMutual

open import QIT.Prelude
open import QIT.Prop
open import QIT.Types
open import QIT.Maybe using (Maybe; nothing; just; just-inj; just≢nothing)
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
  ; ty₁ᴿ = ty₁ᴿ
  ; ∙ᴿ = ≡.refl
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module ε where
  open ≡
  module DA = D.Algebra A
  module G = G₀ A
  module WGA = W.Algebra (G₀ A)
  module FGA = F₀ (G₀ A)
  module DFA = D.Algebra (F₀ (G₀ A))

  conAtom : DFA.Con → G.Atom
  conAtom (γ , kγ) = G.getConAtom γ kγ

  conAtom-isCon : (γ : DFA.Con) → G.[ conAtom γ ]₀ ≡ G.ĉ
  conAtom-isCon (γ , kγ) = G.conKind γ kγ

  conᴿ : DFA.Con → DA.Con
  conᴿ (γ , kγ) = G.getCon γ kγ

  tyAtom : DFA.Ty → G.Atom
  tyAtom (a , ka) = G.getTyAtom a ka

  tyAtom-isTy : (a : DFA.Ty) → G.[ tyAtom a ]₀ ≡ G.t̂
  tyAtom-isTy (a , ka) = G.tyKind a ka

  tyᴿ : DFA.Ty → DA.Ty
  tyᴿ a = G.Ty₀ (tyAtom a) (tyAtom-isTy a)

  ty₁ᴿ : ∀ a → DA.ty₁ (tyᴿ a) ≡ conᴿ (DFA.ty₁ a)
  ty₁ᴿ (a , ka) =
    G.Ty₀₁
      (G.getConAtom (G.ty₁ a) (G.kty₁ a ka))
      (G.getTyAtom a ka)
      (G.conKind (G.ty₁ a) (G.kty₁ a ka))
      (G.tyKind a ka)
      (G.getTy₁-kind (G.ty₁ a) a (G.kty₁ a ka) ka refl)

  ▷ᴿ : ∀ γ a
    → (a₁ : DFA.ty₁ a ≡ γ)
    → (a₁' : DA.ty₁ (tyᴿ a) ≡ conᴿ γ)
    → conᴿ (DFA.▷ γ a a₁) ≡ DA.▷ (conᴿ γ) (tyᴿ a) a₁'
  ▷ᴿ (γ , kγ) (a , ka) a₁ a₁' =
    G.Con₀-▷₀
      (G.getConAtom γ kγ)
      (G.getTyAtom a ka)
      (G.conKind γ kγ)
      (G.tyKind a ka)
      (G.getTy₁-kind γ a kγ ka (cong fst a₁))

  u₀ : (γ : G.Atom) (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → G.Ty₀ (G.u₀ γ kγ) (G.ku₀ γ kγ) ≡ DA.u (G.Con₀ γ kγ)
  u₀ (G.con γ) refl = refl

  uᴿ : (γ : DFA.Con) → tyᴿ (DFA.u γ) ≡ DA.u (conᴿ γ)
  uᴿ γ = u₀ (conAtom γ) (conAtom-isCon γ)

  π₀ : (γ a b : G.Atom)
    → (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → (ka : G.[ a ]₀ ≡ G.t̂)
    → (a₁ : G.ty₁₀ a ka ≡ γ)
    → (kb : G.[ b ]₀ ≡ G.t̂)
    → (b₁ : G.ty₁₀ b kb ≡ G.▷₀ γ a kγ ka a₁)
    → G.Ty₀ (G.π₀ γ a b kγ ka a₁ kb b₁)
               (G.kπ₀ γ a b kγ ka a₁ kb b₁)
    ≡ DA.π (G.Con₀ γ kγ) (G.Ty₀ a ka) (G.Ty₀ b kb)
        (G.Ty₀₁ γ a kγ ka a₁)
        (trans (G.Ty₀₁ (G.▷₀ γ a kγ ka a₁) b
                        (G.k▷₀ γ a kγ ka a₁) kb b₁)
               (G.Con₀-▷₀ γ a kγ ka a₁))
  π₀ (G.con γ) (G.ty a) (G.ty b) kγ ka a₁ kb b₁ = refl

  πᴿ : ∀ γ a b
    → (a₁ : DFA.ty₁ a ≡ γ)
    → (b₁ : DFA.ty₁ b ≡ DFA.▷ γ a a₁)
    → (a₁' : DA.ty₁ (tyᴿ a) ≡ conᴿ γ)
    → (b₁' : DA.ty₁ (tyᴿ b) ≡ DA.▷ (conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (DFA.π γ a b a₁ b₁)
    ≡ DA.π (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  πᴿ (γ , kγ) (a , ka) (b , kb) a₁ b₁ a₁' b₁' =
    π₀ (conAtom (γ , kγ)) (tyAtom (a , ka)) (tyAtom (b , kb))
       (conAtom-isCon (γ , kγ)) (tyAtom-isTy (a , ka))
       (G.getTy₁-kind γ a kγ ka (cong fst a₁))
       (tyAtom-isTy (b , kb))
       (G.getTy₁-kind (G.▷ γ a) b (G.k▷ γ a kγ ka (cong fst a₁)) kb
         (cong fst b₁))

  σ₀ : (γ a b : G.Atom)
    → (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → (ka : G.[ a ]₀ ≡ G.t̂)
    → (a₁ : G.ty₁₀ a ka ≡ γ)
    → (kb : G.[ b ]₀ ≡ G.t̂)
    → (b₁ : G.ty₁₀ b kb ≡ G.▷₀ γ a kγ ka a₁)
    → G.Ty₀ (G.σ₀ γ a b kγ ka a₁ kb b₁)
               (G.kσ₀ γ a b kγ ka a₁ kb b₁)
    ≡ DA.σ (G.Con₀ γ kγ) (G.Ty₀ a ka) (G.Ty₀ b kb)
        (G.Ty₀₁ γ a kγ ka a₁)
        (trans (G.Ty₀₁ (G.▷₀ γ a kγ ka a₁) b
                        (G.k▷₀ γ a kγ ka a₁) kb b₁)
               (G.Con₀-▷₀ γ a kγ ka a₁))
  σ₀ (G.con γ) (G.ty a) (G.ty b) kγ ka a₁ kb b₁ = refl

  σᴿ : ∀ γ a b
    → (a₁ : DFA.ty₁ a ≡ γ)
    → (b₁ : DFA.ty₁ b ≡ DFA.▷ γ a a₁)
    → (a₁' : DA.ty₁ (tyᴿ a) ≡ conᴿ γ)
    → (b₁' : DA.ty₁ (tyᴿ b) ≡ DA.▷ (conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (DFA.σ γ a b a₁ b₁)
    ≡ DA.σ (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  σᴿ (γ , kγ) (a , ka) (b , kb) a₁ b₁ a₁' b₁' =
    σ₀ (conAtom (γ , kγ)) (tyAtom (a , ka)) (tyAtom (b , kb))
       (conAtom-isCon (γ , kγ)) (tyAtom-isTy (a , ka))
       (G.getTy₁-kind γ a kγ ka (cong fst a₁))
       (tyAtom-isTy (b , kb))
       (G.getTy₁-kind (G.▷ γ a) b (G.k▷ γ a kγ ka (cong fst a₁)) kb
         (cong fst b₁))

ε⁻ : ∀ {ℓA} (A : D.Algebra ℓA) → D.Hom A (F₀ (G₀ A))
ε⁻ A = record
  { conᴿ = conᴿ
  ; tyᴿ = tyᴿ
  ; ty₁ᴿ = ty₁ᴿ
  ; ∙ᴿ = ∙ᴿ
  ; ▷ᴿ = ▷ᴿ
  ; uᴿ = uᴿ
  ; πᴿ = πᴿ
  ; σᴿ = σᴿ }
  module ε⁻ where
  open ≡
  module DA = D.Algebra A
  module G = G₀ A
  module DFA = D.Algebra (F₀ (G₀ A))
  module FGA = F₀ (G₀ A)

  ι : G.Atom → G.CT
  ι x = return x

  kcon : (γ : DA.Con) → G.[ ι (G.con γ) ] ≡ G.cʰ
  kcon γ = mk≡↓ (∧i tt* , tt*) tt* refl

  kty : (a : DA.Ty) → G.[ ι (G.ty a) ] ≡ G.tʰ
  kty a = mk≡↓ (∧i tt* , tt*) tt* refl

  ty₁ι : (a : DA.Ty) → G.ty₁ (ι (G.ty a)) ≡ ι (G.con (DA.ty₁ a))
  ty₁ι a = mk≡↓ (∧i tt* , ∧i refl , tt*) tt* refl

  ▷ι : (γ : DA.Con) (a : DA.Ty)
    → (a₁ : DA.ty₁ a ≡ γ)
    → G.▷ (ι (G.con γ)) (ι (G.ty a)) ≡ ι (G.con (DA.▷ γ a a₁))
  ▷ι γ a a₁ = mk≡↓ q tt* refl
    where
    q : G.▷ (ι (G.con γ)) (ι (G.ty a)) ↓
    q = ∧i tt* , ∧i tt* , ∧i refl , ∧i refl , ∧i cong G.con a₁ , tt*

  uι : (γ : DA.Con) → G.u (ι (G.con γ)) ≡ ι (G.ty (DA.u γ))
  uι γ = mk≡↓ q tt* refl
    where
    q : G.u (ι (G.con γ)) .Cond
    q = ∧i tt* , ∧i refl , tt*

  πι : (γ : DA.Con) (a b : DA.Ty)
    → (a₁ : DA.ty₁ a ≡ γ)
    → (b₁ : DA.ty₁ b ≡ DA.▷ γ a a₁)
    → G.π (ι (G.con γ)) (ι (G.ty a)) (ι (G.ty b))
    ≡ ι (G.ty (DA.π γ a b a₁ b₁))
  πι γ a b a₁ b₁ = mk≡↓ q tt* refl
    where
    q : G.π (ι (G.con γ)) (ι (G.ty a)) (ι (G.ty b)) .Cond
    q = ∧i tt* , ∧i tt* , ∧i tt* ,
        ∧i refl , ∧i refl , ∧i cong G.con a₁ ,
        ∧i refl , ∧i cong G.con b₁ , tt*

  σι : (γ : DA.Con) (a b : DA.Ty)
    → (a₁ : DA.ty₁ a ≡ γ)
    → (b₁ : DA.ty₁ b ≡ DA.▷ γ a a₁)
    → G.σ (ι (G.con γ)) (ι (G.ty a)) (ι (G.ty b))
    ≡ ι (G.ty (DA.σ γ a b a₁ b₁))
  σι γ a b a₁ b₁ = mk≡↓ q tt* refl
    where
    q : G.σ (ι (G.con γ)) (ι (G.ty a)) (ι (G.ty b)) .Cond
    q = ∧i tt* , ∧i tt* , ∧i tt* ,
        ∧i refl , ∧i refl , ∧i cong G.con a₁ ,
        ∧i refl , ∧i cong G.con b₁ , tt*

  conᴿ : DA.Con → DFA.Con
  conᴿ γ = ι (G.con γ) , kcon γ

  tyᴿ : DA.Ty → DFA.Ty
  tyᴿ a = ι (G.ty a) , kty a

  ty₁ᴿ : ∀ a → DFA.ty₁ (tyᴿ a) ≡ conᴿ (DA.ty₁ a)
  ty₁ᴿ a = ΣP≡ _ _ (ty₁ι a)

  ∙ᴿ : conᴿ DA.∙ ≡ DFA.∙
  ∙ᴿ = ΣP≡ _ _ refl

  ▷ᴿ : ∀ γ a
    → (a₁ : DA.ty₁ a ≡ γ)
    → (a₁' : DFA.ty₁ (tyᴿ a) ≡ conᴿ γ)
    → conᴿ (DA.▷ γ a a₁) ≡ DFA.▷ (conᴿ γ) (tyᴿ a) a₁'
  ▷ᴿ γ a a₁ a₁' = ΣP≡ _ _ (sym (▷ι γ a a₁))

  uᴿ : ∀ γ → tyᴿ (DA.u γ) ≡ DFA.u (conᴿ γ)
  uᴿ γ = ΣP≡ _ _ (sym (uι γ))

  πᴿ : ∀ γ a b
    → (a₁ : DA.ty₁ a ≡ γ)
    → (b₁ : DA.ty₁ b ≡ DA.▷ γ a a₁)
    → (a₁' : DFA.ty₁ (tyᴿ a) ≡ conᴿ γ)
    → (b₁' : DFA.ty₁ (tyᴿ b) ≡ DFA.▷ (conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (DA.π γ a b a₁ b₁)
    ≡ DFA.π (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  πᴿ γ a b a₁ b₁ a₁' b₁' = ΣP≡ _ _ (sym (πι γ a b a₁ b₁))

  σᴿ : ∀ γ a b
    → (a₁ : DA.ty₁ a ≡ γ)
    → (b₁ : DA.ty₁ b ≡ DA.▷ γ a a₁)
    → (a₁' : DFA.ty₁ (tyᴿ a) ≡ conᴿ γ)
    → (b₁' : DFA.ty₁ (tyᴿ b) ≡ DFA.▷ (conᴿ γ) (tyᴿ a) a₁')
    → tyᴿ (DA.σ γ a b a₁ b₁)
    ≡ DFA.σ (conᴿ γ) (tyᴿ a) (tyᴿ b) a₁' b₁'
  σᴿ γ a b a₁ b₁ a₁' b₁' = ΣP≡ _ _ (sym (σι γ a b a₁ b₁))

εε⁻ : ∀ {ℓA} (A : D.Algebra ℓA) → (ε A D.∘ ε⁻ A) D.≈ D.id
εε⁻ A = D.mk≈ (λ γ → ≡.refl) (λ a → ≡.refl)


ε⁻ε : ∀ {ℓA} (A : D.Algebra ℓA) → (ε⁻ A D.∘ ε A) D.≈ D.id
ε⁻ε A = D.mk≈ con≡ ty≡
  where
  open ≡
  module DA = D.Algebra A
  module G = G₀ A
  module FG = F₀ (G₀ A)
  module DFA = D.Algebra (F₀ (G₀ A))

  ι : G.Atom → G.CT
  ι = ε⁻.ι A

  ι-β : (x : G.CT) → (p : x ↓) → x ≡ ι (x ! p)
  ι-β (P ⊢ f) p = G.mkCT≡ (λ _ → tt*) (λ _ → p) (λ q _ → congp f)

  Ty₀-η : (a : G.Atom)
    → (ka : G.[ a ]₀ ≡ G.t̂)
    → G.ty (G.Ty₀ a ka) ≡ a
  Ty₀-η (G.ty a) refl = refl

  con≡ : (γ : DFA.Con) → (ε⁻ A D.∘ ε A) .D.conᴿ γ ≡ γ
  con≡ γ@(x , kx) = ΣP≡ _ _ p
    where
    open ≡
    witness : x ↓
    witness = G.con↓ x kx
    p : ι (G.con (ε.conᴿ A γ)) ≡ x
    p =
      trans
        (cong ι (G.con-Con₀ (ε.conAtom A γ) (ε.conAtom-isCon A γ)))
        (sym (ι-β x witness))

  ty≡ : (a : DFA.Ty) → (ε⁻ A D.∘ ε A) .D.tyᴿ a ≡ a
  ty≡ a@(a₀ , ka) = ΣP≡ _ _ q
    where
    open ≡
    a↓ : a₀ ↓
    a↓ = G.ty↓ a₀ ka
    q : ι (G.ty (ε.tyᴿ A a)) ≡ a₀
    q =
      trans
        (cong ι
          (Ty₀-η (ε.tyAtom A a) (ε.tyAtom-isTy A a)))
        (sym (ι-β a₀ a↓))

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
  (I : W.Algebra ℓA)
  (recᵂ : (Aᵂ : W.Algebra (lsuc ℓA)) → W.Hom I Aᵂ)
  (recUniqueᵂ : {Aᵂ : W.Algebra (lsuc ℓA)} → (f : W.Hom I Aᵂ) → f W.≈ recᵂ Aᵂ)
  where

  ℓA' = lsuc ℓA
  ℓA'' = lsuc ℓA'

  open ≡-Reasoning
  open ≡

  open import QIT.Examples.ConTy.InitialMutualWT I recᵂ recUniqueᵂ

  -- I↑ = W.LiftAlgebra ℓA' I
  -- module I↑ = W.Algebra (W.LiftAlgebra ℓA' I)

  FI : D.Algebra ℓA
  FI = F₀ I
  module FI = D.Algebra FI
  module F₀I = F₀ I

  -- FI↑ = D.LiftAlgebra ℓA' FI
  -- module FI↑ = D.Algebra (D.LiftAlgebra ℓA' FI)

  GFI : W.Algebra ℓA'
  GFI = G₀ FI
  module G₀FI = G₀ FI
  module GFI = W.Algebra (G₀ FI)

  FGFI : D.Algebra ℓA
  FGFI = F₀ GFI
  module FGFI = D.Algebra FGFI
  module F₀GFI = F₀ GFI

  h : (A : D.Algebra ℓA) → W.Hom I (G₀ A) 
  h A = recᵂ (G₀ A)

  recᴰ : (A : D.Algebra ℓA) → D.Hom FI A
  recᴰ A = ε A D.∘ F₁ (h A)

  module _ {A : D.Algebra ℓA} (f : D.Hom (F₀ I) A) where
    module A = D.Algebra A
    A↑ = D.LiftAlgebra ℓA' A
    module A↑ = D.Algebra (D.LiftAlgebra ℓA' A)

    GA : W.Algebra (lsuc ℓA)
    GA = G₀ A
    module G₀A = G₀ A
    module GA = W.Algebra (G₀ A)

    FGA : D.Algebra (lsuc ℓA)
    FGA = F₀ GA
    module F₀GA = F₀ GA
    module FGA = D.Algebra (F₀ GA)

    ι : W.Hom I GFI
    ι = recᵂ GFI
    module ι = W.Hom ι

    Fι : D.Hom FI FGFI
    Fι = F₁ ι
    module Fι = F₁ ι

    θkγ : {γ : I.CT}
        → I.[ γ ] ≡ I.ĉ
        → G₀FI.[ ι.θ γ ] ≡ G₀FI.cʰ
    θkγ {γ} kγ =
      G₀FI.[ ι.θ γ ]
        ≡⟨ sym ι.[ γ ] ⟩
      ι.θ I.[ γ ]
        ≡⟨ cong ι.θ kγ ⟩
      ι.θ I.ĉ
        ≡⟨ ι.ĉ ⟩
      G₀FI.cʰ ∎

    θka : {γ a : I.CT}
        → I.[ γ ] ≡ I.ĉ
        → I.[ a ] ≡ I.t̂
        → G₀FI.[ ι.θ a ] ≡ G₀FI.tʰ
    θka {γ} {a} kγ ka =
      G₀FI.[ ι.θ a ]
        ≡⟨ sym ι.[ a ] ⟩
      ι.θ I.[ a ]
        ≡⟨ cong ι.θ ka ⟩
      ι.θ I.t̂
        ≡⟨ ι.t̂ ⟩
      G₀FI.tʰ ∎

    Fι∘ε≡id : Fι D.∘ ε FI D.≈ D.id
    Fι∘ε≡id = D.mk≈ {!con≡!} {!ty≡!}
      where
      εFI : D.Hom FGFI FI
      εFI = ε FI
      module εFI = ε FI
      module εFI₀ = D.Hom εFI
      module Classβ where
        open PropDispAlgebra
        module C = W.Algebra CT→Class.DA
        module C-rec = W.Hom (recᵂ CT→Class.DA)

        classθ : ∀ x → C-rec.θ x ≡ CT→Class x
        classθ x = refl

        ty₁-arg↓ : ∀ a → ι.θ (I.ty₁ a) ↓ → ι.θ a ↓
        ty₁-arg↓ a ty₁a↓ =
          G₀FI.ty₁⁻ (ι.θ a) (transp↓ (ι.ty₁ a) ty₁a↓)

        ty₁-arg-kind : ∀ a (ty₁a↓ : ι.θ (I.ty₁ a) ↓)
          → G₀FI.[ ι.θ a ] ≡ G₀FI.tʰ
        ty₁-arg-kind a ty₁a↓ =
          mk≡↓ (G₀FI.[]↓ (ι.θ a) a↓) tt* (ty₁θa↓ .∧e₂ .∧e₁)
          where
          ty₁θa↓ : G₀FI.ty₁ (ι.θ a) ↓
          ty₁θa↓ = transp↓ (ι.ty₁ a) ty₁a↓
          a↓ : ι.θ a ↓
          a↓ = G₀FI.ty₁⁻ (ι.θ a) ty₁θa↓

        Classβ : I.CT → Prop _
        Classβ x = ι.θ x ↓
          → just I.[ x ]
          ≡ Class→CT (CT→Class x)

        βA : PropDispAlgebra ℓA'
        module βA = PropDispAlgebra βA
        βA .CT = Classβ
        βA .[] x xβ [θx]↓ =
          just I.[ I.[ x ] ]
            ≡⟨ refl ⟩
          QIT.Maybe.map I.[_] (just I.[ x ])
            ≡⟨ cong (QIT.Maybe.map I.[_]) (xβ θx↓) ⟩
          QIT.Maybe.map I.[_] (Class→CT (CT→Class x))
            ≡⟨ class[]β (CT→Class x) ⟩
          Class→CT (C.[ CT→Class x ])
            ≡⟨ cong Class→CT (sym (C-rec.[ x ])) ⟩
          Class→CT (CT→Class I.[ x ]) ∎
          where
          θx↓ : ι.θ x ↓
          θx↓ = G₀FI.[]⁻ (ι.θ x) (transp↓ (ι.[ x ]) [θx]↓)

          class[]β : ∀ c
            → QIT.Maybe.map I.[_] (Class→CT c) ≡ Class→CT (C.[ c ])
          class[]β # = refl
          class[]β ([]k̂ k₀) = cong just I.kk̂
          class[]β ([]k̂ c₀) = cong just I.kk̂
          class[]β ([]k̂ t₀) = cong just I.kk̂
          class[]β []ĉ = cong just I.kĉ
          class[]β []t̂ = cong just I.kt̂
        βA .k̂ k↓ =
          just I.[ I.k̂ ]
            ≡⟨ cong just I.kk̂ ⟩
          just I.k̂
            ≡⟨ refl ⟩
          Class→CT ([]k̂ k₀)
            ≡⟨ cong Class→CT (sym C-rec.k̂) ⟩
          Class→CT (CT→Class I.k̂) ∎
        βA .ĉ c↓ =
          just I.[ I.ĉ ]
            ≡⟨ cong just I.kĉ ⟩
          just I.k̂
            ≡⟨ refl ⟩
          Class→CT ([]k̂ c₀)
            ≡⟨ cong Class→CT (sym C-rec.ĉ) ⟩
          Class→CT (CT→Class I.ĉ) ∎
        βA .t̂ t↓ =
          just I.[ I.t̂ ]
            ≡⟨ cong just I.kt̂ ⟩
          just I.k̂
            ≡⟨ refl ⟩
          Class→CT ([]k̂ t₀)
            ≡⟨ cong Class→CT (sym C-rec.t̂) ⟩
          Class→CT (CT→Class I.t̂) ∎
        βA .ty₁ a aβ ty₁a↓ with inspect (CT→Class a)
        ... | # , q = ⊥e (just≢nothing p)
          where
          p : just I.[ a ] ≡ Class→CT #
          p = trans (aβ (ty₁-arg↓ a ty₁a↓)) (cong Class→CT (sym q))
        ... | []k̂ k₀ , q = ⊥e (G₀FI.kʰ≢tʰ (trans (sym kind) (ty₁-arg-kind a ty₁a↓)))
          where
          p : just I.[ a ] ≡ Class→CT ([]k̂ k₀)
          p = trans (aβ (ty₁-arg↓ a ty₁a↓)) (cong Class→CT (sym q))
          source : I.[ a ] ≡ I.k̂
          source = just-inj p
          kind : G₀FI.[ ι.θ a ] ≡ G₀FI.kʰ
          kind = trans (sym (ι.[ a ])) (trans (cong ι.θ source) ι.k̂)
        ... | []k̂ c₀ , q = ⊥e (G₀FI.kʰ≢tʰ (trans (sym kind) (ty₁-arg-kind a ty₁a↓)))
          where
          p : just I.[ a ] ≡ Class→CT ([]k̂ c₀)
          p = trans (aβ (ty₁-arg↓ a ty₁a↓)) (cong Class→CT (sym q))
          source : I.[ a ] ≡ I.k̂
          source = just-inj p
          kind : G₀FI.[ ι.θ a ] ≡ G₀FI.kʰ
          kind = trans (sym (ι.[ a ])) (trans (cong ι.θ source) ι.k̂)
        ... | []k̂ t₀ , q = ⊥e (G₀FI.kʰ≢tʰ (trans (sym kind) (ty₁-arg-kind a ty₁a↓)))
          where
          p : just I.[ a ] ≡ Class→CT ([]k̂ t₀)
          p = trans (aβ (ty₁-arg↓ a ty₁a↓)) (cong Class→CT (sym q))
          source : I.[ a ] ≡ I.k̂
          source = just-inj p
          kind : G₀FI.[ ι.θ a ] ≡ G₀FI.kʰ
          kind = trans (sym (ι.[ a ])) (trans (cong ι.θ source) ι.k̂)
        ... | []ĉ , q = ⊥e (G₀FI.cʰ≢tʰ (trans (sym kind) (ty₁-arg-kind a ty₁a↓)))
          where
          p : just I.[ a ] ≡ Class→CT []ĉ
          p = trans (aβ (ty₁-arg↓ a ty₁a↓)) (cong Class→CT (sym q))
          source : I.[ a ] ≡ I.ĉ
          source = just-inj p
          kind : G₀FI.[ ι.θ a ] ≡ G₀FI.cʰ
          kind = trans (sym (ι.[ a ])) (trans (cong ι.θ source) ι.ĉ)
        ... | []t̂ , q =
          just I.[ I.ty₁ a ]
            ≡⟨ cong just (I.kty₁ a source) ⟩
          just I.ĉ
            ≡⟨ refl ⟩
          Class→CT []ĉ
            ≡⟨ cong Class→CT (sym (cong C.ty₁ θ≡)) ⟩
          Class→CT (C.ty₁ (C-rec.θ a))
            ≡⟨ cong Class→CT (sym (C-rec.ty₁ a)) ⟩
          Class→CT (CT→Class (I.ty₁ a)) ∎
          where
          p : just I.[ a ] ≡ Class→CT []t̂
          p = trans (aβ (ty₁-arg↓ a ty₁a↓)) (cong Class→CT (sym q))
          source : I.[ a ] ≡ I.t̂
          source = just-inj p
          θ≡ : C-rec.θ a ≡ []t̂
          θ≡ = trans (classθ a) (sym q)
        βA .∙ ∙↓ =
          just I.[ I.∙ ]
            ≡⟨ cong just I.k∙ ⟩
          just I.ĉ
            ≡⟨ refl ⟩
          Class→CT []ĉ
            ≡⟨ cong Class→CT (sym C-rec.∙) ⟩
          Class→CT (CT→Class I.∙) ∎
        βA .▷ γ a γβ aβ θ▷↓ =
          just I.[ I.▷ γ a ]
            ≡⟨ cong just (I.k▷ γ a kγ ka a₁) ⟩
          just I.ĉ
            ≡⟨ {!!} ⟩
          Class→CT (CT→Class (I.▷ γ a)) ∎
          where
          θγ↓ : ι.θ γ ↓
          θγ↓ = {!!}
          kγ : I.[ γ ] ≡ I.ĉ
          kγ = {!!}
          ka : I.[ a ] ≡ I.t̂
          a₁ : I.ty₁ a ≡ γ
          v : ι.θ (I.▷ γ a) ≡ G₀FI.▷ (ι.θ γ) (ι.θ a)
          v = ι.▷ γ a kγ ka a₁ 
        βA .u = {!!}
        βA .π = {!!}
        βA .σ = {!!}
