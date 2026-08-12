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
      open DispAlgebra
      module Beta where
        record Beta (x : I.CT) : Set _ where
          constructor mkBeta
          eta-equality
          field
            conβ : (kx : I.[ x ] ≡ I.ĉ)
              → ι.θ x ≡ return (G₀.con (x , kx))

            tyβ : (kx : I.[ x ] ≡ I.t̂)
              → ι.θ x ≡ return (G₀.ty (x , kx))

        open Beta

        isPropBeta : ∀ {x} → isProp (Beta x)
        isPropBeta {x} βA βB = refl

        isPropBeta* : ∀ {x y}
          → (p : x ≡ y)
          → (xβ : Beta x) (yβ : Beta y)
          → subst Beta p xβ ≡ yβ
        isPropBeta* {x} {y} refl xβ yβ = refl

        θ-con-kind : ∀ {x}
          → I.[ x ] ≡ I.ĉ
          → G₀FI.[ ι.θ x ] ≡ G₀FI.cʰ
        θ-con-kind = θkγ

        θ-ty-kind : ∀ {x}
          → I.[ x ] ≡ I.t̂
          → G₀FI.[ ι.θ x ] ≡ G₀FI.tʰ
        θ-ty-kind {x} kx =
          G₀FI.[ ι.θ x ]
            ≡⟨ sym ι.[ x ] ⟩
          ι.θ I.[ x ]
            ≡⟨ cong ι.θ kx ⟩
          ι.θ I.t̂
            ≡⟨ ι.t̂ ⟩
          G₀FI.tʰ ∎
          
        θ-con↓ : ∀ {x}
          → I.[ x ] ≡ I.ĉ
          → ι.θ x ↓
        θ-con↓ {x} kx = G₀FI.con↓ (ι.θ x) (θ-con-kind kx)
          
        θ-ty↓ : ∀ {x}
          → I.[ x ] ≡ I.t̂
          → ι.θ x ↓
        θ-ty↓ {x} kx = G₀FI.ty↓ (ι.θ x) (θ-ty-kind kx)

        conBeta : ∀ {x}
          → (ι.θ x ↓ → G₀FI.[ ι.θ x ] ≡ G₀FI.cʰ)
          → (∀ (kx : I.[ x ] ≡ I.ĉ)
              → ι.θ x ≡ return (G₀FI.con (x , kx)))
          → Beta x
        conBeta {x} isCon cβ = mkBeta cβ tβ
          where
          tβ : (kx : I.[ x ] ≡ I.t̂)
            → ι.θ x ≡ return (G₀FI.ty (x , kx))
          tβ kx = ⊥e (G₀FI.cʰ≢tʰ
            (trans (sym (isCon (θ-ty↓ kx))) (θ-ty-kind kx)))

        -- conBeta : ∀ {x}
        --   → (ι.θ x ↓ → G₀FI.[ ι.θ x ] ≡ G₀FI.cʰ)
        --   → (∀ (kx : I.[ x ] ≡ I.ĉ)
        --       → G₀FI.[]≡cʰ→Con (ι.θ x) (θ-con-kind kx) ≡ (x , kx))
        --   → Beta x
        -- conBeta {x} isCon conβ = mkBeta cβ tβ
        --   where
        --   cβ : (kx : I.[ x ] ≡ I.ĉ)
        --     → ι.θ x ≡ return (G₀FI.con (x , kx))
        --   cβ kx =
        --     trans
        --       (G₀FI.[]≡cʰ-beta (ι.θ x) (θ-con-kind kx))
        --       (cong (return ∘ G₀FI.con) (conβ kx))
        --   tβ : (kx : I.[ x ] ≡ I.t̂)
        --     → ι.θ x ≡ return (G₀FI.ty (x , kx))
        --   tβ kx = ⊥e (G₀FI.cʰ≢tʰ
        --     (trans (sym (isCon (θ-ty↓ kx))) (θ-ty-kind kx)))

        tyBeta : ∀ {x}
          → (ι.θ x ↓ → G₀FI.[ ι.θ x ] ≡ G₀FI.tʰ)
          → (∀ (kx : I.[ x ] ≡ I.t̂)
              → G₀FI.[]≡tʰ→Ty (ι.θ x) (θ-ty-kind kx) ≡ (x , kx))
          → Beta x
        tyBeta {x} isTy tyβ = mkBeta cβ tβ
          where
          cβ : (kx : I.[ x ] ≡ I.ĉ)
            → ι.θ x ≡ return (G₀FI.con (x , kx))
          cβ kx = ⊥e (G₀FI.cʰ≢tʰ
            (trans (sym (θ-con-kind kx)) (isTy (θ-con↓ kx))))
          tβ : (kx : I.[ x ] ≡ I.t̂)
            → ι.θ x ≡ return (G₀FI.ty (x , kx))
          tβ kx =
            trans
              (G₀FI.[]≡tʰ-beta (ι.θ x) (θ-ty-kind kx))
              (cong (return ∘ G₀FI.ty) (tyβ kx))

        absurdBeta : ∀ {x}
          → (ι.θ x ↓ → G₀FI.[ ι.θ x ] ≡ G₀FI.cʰ → ⊥)
          → (ι.θ x ↓ → G₀FI.[ ι.θ x ] ≡ G₀FI.tʰ → ⊥)
          → Beta x
        absurdBeta ¬c ¬t =
          mkBeta
            (λ kx → ⊥e (¬c (θ-con↓ kx) (θ-con-kind kx)))
            (λ kx → ⊥e (¬t (θ-ty↓ kx) (θ-ty-kind kx)))

        βA : DispAlgebra ℓA'
        module βA = DispAlgebra βA
        βA .CT x = Beta x
        βA .[] x β = absurdBeta ¬c ¬t
          where
          θx↓ : ι.θ I.[ x ] ↓ → ι.θ x ↓
          θx↓ θ[x]↓ = G₀FI.[]⁻ (ι.θ x) (transp↓ (ι.[ x ]) θ[x]↓)
          [[x]]≡kʰ : ι.θ I.[ x ] ↓ → G₀FI.[ ι.θ I.[ x ] ] ≡ G₀FI.kʰ
          [[x]]≡kʰ θ[x]↓ =
            G₀FI.[ ι.θ I.[ x ] ]
              ≡⟨ cong G₀FI.[_] (ι.[ x ]) ⟩
            G₀FI.[ G₀FI.[ ι.θ x ] ]
              ≡⟨ G₀FI.[[x]]≡kʰ (ι.θ x) (θx↓ θ[x]↓) ⟩
            G₀FI.kʰ ∎
          ¬c : ι.θ I.[ x ] ↓ → G₀FI.[ ι.θ I.[ x ] ] ≡ G₀FI.cʰ → ⊥
          ¬c θ[x]↓ k[x] = G₀FI.kʰ≢cʰ (trans (sym ([[x]]≡kʰ θ[x]↓)) k[x])
          ¬t : ι.θ I.[ x ] ↓ → G₀FI.[ ι.θ I.[ x ] ] ≡ G₀FI.tʰ → ⊥
          ¬t θ[x]↓ k[x] = G₀FI.kʰ≢tʰ (trans (sym ([[x]]≡kʰ θ[x]↓)) k[x])
        βA .ĉ = absurdBeta ¬c ¬t
          where
          kind : G₀FI.[ ι.θ I.ĉ ] ≡ G₀FI.kʰ
          kind = trans (cong G₀FI.[_] ι.ĉ) G₀FI.kĉ
          ¬c : ι.θ I.ĉ ↓ → G₀FI.[ ι.θ I.ĉ ] ≡ G₀FI.cʰ → ⊥
          ¬c _ kc = G₀FI.kʰ≢cʰ (trans (sym kind) kc)
          ¬t : ι.θ I.ĉ ↓ → G₀FI.[ ι.θ I.ĉ ] ≡ G₀FI.tʰ → ⊥
          ¬t _ kt = G₀FI.kʰ≢tʰ (trans (sym kind) kt)
        βA .t̂ = absurdBeta ¬c ¬t
          where
          kind : G₀FI.[ ι.θ I.t̂ ] ≡ G₀FI.kʰ
          kind = trans (cong G₀FI.[_] ι.t̂) G₀FI.kt̂
          ¬c : ι.θ I.t̂ ↓ → G₀FI.[ ι.θ I.t̂ ] ≡ G₀FI.cʰ → ⊥
          ¬c _ kc = G₀FI.kʰ≢cʰ (trans (sym kind) kc)
          ¬t : ι.θ I.t̂ ↓ → G₀FI.[ ι.θ I.t̂ ] ≡ G₀FI.tʰ → ⊥
          ¬t _ kt = G₀FI.kʰ≢tʰ (trans (sym kind) kt)
        βA .k̂ = absurdBeta ¬c ¬t
          where
          kind : G₀FI.[ ι.θ I.k̂ ] ≡ G₀FI.kʰ
          kind = trans (cong G₀FI.[_] ι.k̂) G₀FI.kk̂
          ¬c : ι.θ I.k̂ ↓ → G₀FI.[ ι.θ I.k̂ ] ≡ G₀FI.cʰ → ⊥
          ¬c _ kc = G₀FI.kʰ≢cʰ (trans (sym kind) kc)
          ¬t : ι.θ I.k̂ ↓ → G₀FI.[ ι.θ I.k̂ ] ≡ G₀FI.tʰ → ⊥
          ¬t _ kt = G₀FI.kʰ≢tʰ (trans (sym kind) kt)
        βA .kk̂ = isPropBeta* I.kk̂ (βA.[] I.k̂ βA.k̂) βA.k̂
        βA .kĉ = isPropBeta* I.kĉ (βA.[] I.ĉ βA.ĉ) βA.k̂
        βA .kt̂ = isPropBeta* I.kt̂ (βA.[] I.t̂ βA.t̂) βA.k̂
        βA .ty₁ a aβ = {!conBeta isCon cβ!}
          where
          isCon : ι.θ (I.ty₁ a) ↓
            → G₀FI.[ ι.θ (I.ty₁ a) ] ≡ G₀FI.cʰ
          isCon θty₁a↓ =
            trans (cong G₀FI.[_] (ι.ty₁ a)) (G₀FI.kty₁ (ι.θ a) ka)
            where
            ty₁a↓ : G₀FI.ty₁ (ι.θ a) ↓
            ty₁a↓ = transp↓ (ι.ty₁ a) θty₁a↓
            a↓ : ι.θ a ↓
            a↓ = G₀FI.ty₁⁻ (ι.θ a) ty₁a↓
            ka : G₀FI.[ ι.θ a ] ≡ G₀FI.tʰ
            ka = mk≡↓ (G₀FI.[]↓ (ι.θ a) a↓) tt* (ty₁a↓ .∧e₂ .∧e₁)
          cβ : ∀ kx
            → G₀FI.[]≡cʰ→Con (ι.θ (I.ty₁ a)) (θ-con-kind kx)
            ≡ (I.ty₁ a , kx)
          cβ kx =
            G₀FI.[]≡cʰ→Con (ι.θ (I.ty₁ a)) (θ-con-kind kx)
              ≡⟨ dcongsp G₀FI.[]≡cʰ→Con ty₁β ⟩
            G₀FI.[]≡cʰ→Con (return (G₀FI.con (I.ty₁ a , kx))) kreturn
              ≡⟨ refl ⟩
            I.ty₁ a , kx ∎
            where
            ka : I.[ a ] ≡ I.t̂
            ka = I.kty₁-a a kx
            kreturn : G₀FI.[ return (G₀FI.con (I.ty₁ a , kx)) ] ≡ G₀FI.cʰ
            kreturn = mk≡↓ (∧i tt* , tt*) tt* refl
            ty₁β : ι.θ (I.ty₁ a)
              ≡ return (G₀FI.con (I.ty₁ a , kx))
            ty₁β =
              trans
                (ι.ty₁ a)
                (trans
                  (cong G₀FI.ty₁ (aβ .tyβ ka))
                  (mk≡↓ (∧i tt* , ∧i refl , tt*) tt*
                    (cong G₀FI.con (ΣP≡ _ _ refl))))
        βA .kty₁ a aβ ka = refl
        βA .kty₁-a a aβ ka =
          isPropBeta* (I.kty₁-a a ka) (βA.[] a aβ) βA.t̂
        βA .∙ = conBeta isCon cβ
          where
          isCon : ι.θ I.∙ ↓ → G₀FI.[ ι.θ I.∙ ] ≡ G₀FI.cʰ
          isCon _ = trans (cong G₀FI.[_] ι.∙) G₀FI.k∙
          cβ : (k∙ : I.[ I.∙ ] ≡ I.ĉ) → ι.θ I.∙ ≡ return (G₀FI.con (I.∙ , k∙))
          cβ k∙ = ι.∙
        βA .k∙ = isPropBeta* I.k∙ (βA.[] I.∙ βA.∙) βA.ĉ
        βA .▷ γ a γβ aβ = conBeta isCon cβ
          where
          isCon : ι.θ (I.▷ γ a) ↓ → G₀FI.[ ι.θ (I.▷ γ a) ] ≡ G₀FI.cʰ
          isCon θ▷↓ =
            G₀FI.[ ι.θ (I.▷ γ a) ]
              ≡⟨ cong G₀FI.[_] (ι.▷ γ a kγ ka a₁) ⟩
            G₀FI.[ G₀FI.▷ (ι.θ γ) (ι.θ a) ]
              ≡⟨ {!!} ⟩
            G₀FI.cʰ ∎
            where
            θγ↓ : ι.θ γ ≡ return {!!} 
            θγ↓ = {!!}
            kγ : I.[ γ ] ≡ I.ĉ
            kγ = {!!}
            ka : {!!}
            ka = {!!}
            a₁ : {!!}
            a₁ = {!!}
          -- cβ : (k▷ : I.[ I.▷ γ a ] ≡ I.ĉ)
          --   → G₀FI.[]≡cʰ→Con (ι.θ (I.▷ γ a)) (θ-con-kind k▷) ≡ (I.▷ γ a , k▷)
          -- cβ k▷ =
          --   ι.θ (I.▷ γ a)
          --     ≡⟨ ι.▷ γ a kγ ka a₁ ⟩
          --   G₀FI.▷ (ι.θ γ) (ι.θ a)
          --     ≡⟨ cong₂ G₀FI.▷ (γβ .conβ kγ) (aβ .tyβ ka) ⟩
          --   G₀FI.▷ (return (G₀FI.con (γ , kγ)))
          --           (return (G₀FI.ty (a , ka)))
          --     ≡⟨ G₀FI.▷≡return
          --           (G₀FI.con (γ , kγ))
          --           (G₀FI.ty (a , ka))
          --           refl refl (cong G₀FI.con (ΣP≡ _ _ a₁)) ⟩
          --   return (G₀FI.con (I.▷ γ a , k▷)) ∎
          --   where
          --   kγ : I.[ γ ] ≡ I.ĉ
          --   kγ = I.▷-γ γ a k▷
          --   ka : I.[ a ] ≡ I.t̂
          --   ka = I.▷-a γ a k▷
          --   a₁ : I.ty₁ a ≡ γ
          --   a₁ = I.▷-a₁ γ a k▷
          cβ : (k▷ : I.[ I.▷ γ a ] ≡ I.ĉ)
            → ι.θ (I.▷ γ a) ≡ return (G₀FI.con (I.▷ γ a , k▷))
          cβ k▷ =
            ι.θ (I.▷ γ a)
              ≡⟨ ι.▷ γ a kγ ka a₁ ⟩
            G₀FI.▷ (ι.θ γ) (ι.θ a)
              ≡⟨ cong₂ G₀FI.▷ (γβ .conβ kγ) (aβ .tyβ ka) ⟩
            G₀FI.▷ (return (G₀FI.con (γ , kγ)))
                    (return (G₀FI.ty (a , ka)))
              ≡⟨ G₀FI.▷≡return
                    (G₀FI.con (γ , kγ))
                    (G₀FI.ty (a , ka))
                    refl refl (cong G₀FI.con (ΣP≡ _ _ a₁)) ⟩
            return (G₀FI.con (I.▷ γ a , k▷)) ∎
            where
            kγ : I.[ γ ] ≡ I.ĉ
            kγ = I.▷-γ γ a k▷
            ka : I.[ a ] ≡ I.t̂
            ka = I.▷-a γ a k▷
            a₁ : I.ty₁ a ≡ γ
            a₁ = I.▷-a₁ γ a k▷
        βA .k▷ γ a γβ aβ kγ ka a₁ =
          isPropBeta* (I.k▷ γ a kγ ka a₁)
            (βA.[] (I.▷ γ a) (βA.▷ γ a γβ aβ)) βA.ĉ
        βA .▷-γ γ a γβ k▷ =
          isPropBeta* (I.▷-γ γ a k▷) (βA.[] γ γβ) βA.ĉ
        βA .▷-a γ a aβ k▷ =
          isPropBeta* (I.▷-a γ a k▷) (βA.[] a aβ) βA.t̂
        βA .▷-a₁ γ a γβ aβ k▷ =
          isPropBeta* (I.▷-a₁ γ a k▷) (βA.ty₁ a aβ) γβ
        βA .u γ γβ = mkBeta {!!} tβ
          where
          tβ : (ku : I.[ I.u γ ] ≡ I.t̂)
            → ι.θ (I.u γ) ≡ return (G₀FI.ty (I.u γ , ku))
          tβ ku =
            ι.θ (I.u γ)
              ≡⟨ ι.u γ kγ ⟩
            G₀FI.u (ι.θ γ)
              ≡⟨ cong G₀FI.u (γβ .conβ kγ) ⟩
            G₀FI.u (return (G₀FI.con (γ , kγ)))
              ≡⟨ G₀FI.u≡return (G₀FI.con (γ , kγ)) refl ⟩
            return (G₀FI.ty (I.u γ , ku)) ∎
            where
            kγ : I.[ γ ] ≡ I.ĉ
            kγ = I.u-γ γ ku
        βA .ku γ γβ kγ =
          isPropBeta* (I.ku γ kγ) (βA.[] (I.u γ) (βA.u γ γβ)) βA.t̂
        βA .u₁ γ γβ kγ =
          isPropBeta* (I.u₁ γ kγ) (βA.ty₁ (I.u γ) (βA.u γ γβ)) γβ
        βA .u-γ γ γβ ku =
          isPropBeta* (I.u-γ γ ku) (βA.[] γ γβ) βA.ĉ
        βA .π γ a b γβ aβ bβ = mkBeta {!!} tβ
          where
          tβ : (kπ : I.[ I.π γ a b ] ≡ I.t̂)
            → ι.θ (I.π γ a b) ≡ return (G₀FI.ty (I.π γ a b , kπ))
          tβ kπ =
            ι.θ (I.π γ a b)
              ≡⟨ ι.π γ a b kγ ka a₁ kb b₁ ⟩
            G₀FI.π (ι.θ γ) (ι.θ a) (ι.θ b)
              ≡⟨ cong₃ G₀FI.π (γβ .conβ kγ) (aβ .tyβ ka) (bβ .tyβ kb) ⟩
            G₀FI.π (return (G₀FI.con (γ , kγ)))
                    (return (G₀FI.ty (a , ka)))
                    (return (G₀FI.ty (b , kb)))
              ≡⟨ G₀FI.π≡return
                    (G₀FI.con (γ , kγ))
                    (G₀FI.ty (a , ka))
                    (G₀FI.ty (b , kb))
                    refl refl (cong G₀FI.con (ΣP≡ _ _ a₁))
                    refl (cong G₀FI.con (ΣP≡ _ _ b₁)) ⟩
            return (G₀FI.ty (I.π γ a b , kπ)) ∎
            where
            kγ = I.π-γ γ a b kπ
            ka = I.π-a γ a b kπ
            a₁ = I.π-a₁ γ a b kπ
            kb = I.π-b γ a b kπ
            b₁ = I.π-b₁ γ a b kπ
        βA .kπ γ a b γβ aβ bβ kγ ka a₁ kb b₁ =
          isPropBeta* (I.kπ γ a b kγ ka a₁ kb b₁)
            (βA.[] (I.π γ a b) (βA.π γ a b γβ aβ bβ)) βA.t̂
        βA .π₁ γ a b γβ aβ bβ kπ =
          isPropBeta* (I.π₁ γ a b kπ)
            (βA.ty₁ (I.π γ a b) (βA.π γ a b γβ aβ bβ)) γβ
        βA .π-γ γ a b γβ kπ =
          isPropBeta* (I.π-γ γ a b kπ) (βA.[] γ γβ) βA.ĉ
        βA .π-a γ a b aβ kπ =
          isPropBeta* (I.π-a γ a b kπ) (βA.[] a aβ) βA.t̂
        βA .π-a₁ γ a b γβ aβ kπ =
          isPropBeta* (I.π-a₁ γ a b kπ) (βA.ty₁ a aβ) γβ
        βA .π-b γ a b bβ kπ =
          isPropBeta* (I.π-b γ a b kπ) (βA.[] b bβ) βA.t̂
        βA .π-b₁ γ a b γβ aβ bβ kπ =
          isPropBeta* (I.π-b₁ γ a b kπ) (βA.ty₁ b bβ)
            (βA.▷ γ a γβ aβ)
        βA .σ γ a b γβ aβ bβ = mkBeta {!!} tβ
          where
          tβ : (kσ : I.[ I.σ γ a b ] ≡ I.t̂)
            → ι.θ (I.σ γ a b) ≡ return (G₀FI.ty (I.σ γ a b , kσ))
          tβ kσ =
            ι.θ (I.σ γ a b)
              ≡⟨ ι.σ γ a b kγ ka a₁ kb b₁ ⟩
            G₀FI.σ (ι.θ γ) (ι.θ a) (ι.θ b)
              ≡⟨ cong₃ G₀FI.σ (γβ .conβ kγ) (aβ .tyβ ka) (bβ .tyβ kb) ⟩
            G₀FI.σ (return (G₀FI.con (γ , kγ)))
                    (return (G₀FI.ty (a , ka)))
                    (return (G₀FI.ty (b , kb)))
              ≡⟨ G₀FI.σ≡return
                    (G₀FI.con (γ , kγ))
                    (G₀FI.ty (a , ka))
                    (G₀FI.ty (b , kb))
                    refl refl (cong G₀FI.con (ΣP≡ _ _ a₁))
                    refl (cong G₀FI.con (ΣP≡ _ _ b₁)) ⟩
            return (G₀FI.ty (I.σ γ a b , kσ)) ∎
            where
            kγ = I.σ-γ γ a b kσ
            ka = I.σ-a γ a b kσ
            a₁ = I.σ-a₁ γ a b kσ
            kb = I.σ-b γ a b kσ
            b₁ = I.σ-b₁ γ a b kσ
        βA .kσ γ a b γβ aβ bβ kγ ka a₁ kb b₁ =
          isPropBeta* (I.kσ γ a b kγ ka a₁ kb b₁)
            (βA.[] (I.σ γ a b) (βA.σ γ a b γβ aβ bβ)) βA.t̂
        βA .σ₁ γ a b γβ aβ bβ kσ =
          isPropBeta* (I.σ₁ γ a b kσ)
            (βA.ty₁ (I.σ γ a b) (βA.σ γ a b γβ aβ bβ)) γβ
        βA .σ-γ γ a b γβ kσ =
          isPropBeta* (I.σ-γ γ a b kσ) (βA.[] γ γβ) βA.ĉ
        βA .σ-a γ a b aβ kσ =
          isPropBeta* (I.σ-a γ a b kσ) (βA.[] a aβ) βA.t̂
        βA .σ-a₁ γ a b γβ aβ kσ =
          isPropBeta* (I.σ-a₁ γ a b kσ) (βA.ty₁ a aβ) γβ
        βA .σ-b γ a b bβ kσ =
          isPropBeta* (I.σ-b γ a b kσ) (βA.[] b bβ) βA.t̂
        βA .σ-b₁ γ a b γβ aβ bβ kσ =
          isPropBeta* (I.σ-b₁ γ a b kσ) (βA.ty₁ b bβ)
            (βA.▷ γ a γβ aβ)
        βA .σ▷ γ a b γβ aβ bβ kγ ka a₁ kb b₁ =
          isPropBeta* (I.σ▷ γ a b kγ ka a₁ kb b₁)
            (βA.▷ (I.▷ γ a) b (βA.▷ γ a γβ aβ) bβ)
            (βA.▷ γ (I.σ γ a b) γβ (βA.σ γ a b γβ aβ bβ))
        βA .σπ γ a b c γβ aβ bβ cβ kγ ka a₁ kb b₁ kc c₁ =
          isPropBeta* (I.σπ γ a b c kγ ka a₁ kb b₁ kc c₁)
            (βA.π γ a (I.π (I.▷ γ a) b c)
              γβ aβ (βA.π (I.▷ γ a) b c (βA.▷ γ a γβ aβ) bβ cβ))
            (βA.π γ (I.σ γ a b) c
              γβ (βA.σ γ a b γβ aβ bβ) cβ)
{-
        βA .CT = Beta
        βA .[] x β .conβ kx = ⊥e {!G₀FI.[[x]]≢cʰ {ι.θ x} q!}
          where
          q : G₀FI.[ G₀FI.[ ι.θ x ] ] ≡ G₀FI.cʰ
          q = trans (cong G₀FI.[_] (sym ι.[ x ])) (θkγ kx)
        βA .[] x β .tyβ γ kγ k[x] =
          ⊥e {!G₀FI.[[x]]≢tʰ {ι.θ x} {ι.θ γ} θx↓ q!}
          where
          θγ↓ : ι.θ γ ↓
          θγ↓ = G₀FI.con↓ (ι.θ γ) (θkγ kγ)
          q : G₀FI.[ G₀FI.[ ι.θ x ] ] ≡ G₀FI.tʰ (ι.θ γ)
          q =
            G₀FI.[ G₀FI.[ ι.θ x ] ]
              ≡⟨ cong G₀FI.[_] (sym ι.[ x ]) ⟩
            G₀FI.[ ι.θ I.[ x ] ]
              ≡⟨ θka kγ k[x] ⟩
            G₀FI.tʰ (ι.θ γ) ∎
          q≈ : G₀FI.[ G₀FI.[ ι.θ x ] ] ≈ G₀FI.tʰ (ι.θ γ)
          q≈ = ≡→≈ q
          θx↓ : ι.θ x ↓
          θx↓ = (q≈ .∧e₁ .∧e₂ (∧i tt* , θγ↓)) .∧e₂ .∧e₂
        {-
        βA .k̂ .conβ kx = ⊥e (G₀FI.kʰ≢cʰ q)
          where
          r : G₀FI.[ G₀FI.kʰ ] ≡ G₀FI.kʰ
          r = G₀FI.[kʰ]≡kʰ 
          q : G₀FI.kʰ ≡ G₀FI.cʰ
          q = trans (sym r) (trans (cong G₀FI.[_] (sym ι.k̂)) (θkγ kx))
        βA .k̂ .tyβ γ kγ kx = ⊥e (G₀FI.[kʰ]≢tʰ {x* = ι.θ γ} q)
          where
          q : G₀FI.[ G₀FI.kʰ ] ≡ G₀FI.tʰ (ι.θ γ)
          q = trans (cong G₀FI.[_] (sym ι.k̂)) (θka kγ kx)
        βA .kk̂ = refl 
        βA .ĉ .conβ kx = ⊥e (G₀FI.kʰ≢cʰ q)
          where
          q : G₀FI.kʰ ≡ G₀FI.cʰ
          q = trans (sym G₀FI.kĉ) (trans (cong G₀FI.[_] (sym ι.ĉ)) (θkγ kx))
        βA .ĉ .tyβ γ kγ kx = ⊥e (G₀FI.[cʰ]≢tʰ {x* = ι.θ γ} q)
          where
          q : G₀FI.[ G₀FI.cʰ ] ≡ G₀FI.tʰ (ι.θ γ)
          q = trans (cong G₀FI.[_] (sym ι.ĉ)) (θka kγ kx)
        βA .kĉ = refl
        βA .t̂ x β .conβ kx = ⊥e (G₀FI.[tʰ]≢cʰ {x* = ι.θ x}
                                  (trans (cong G₀FI.[_] (sym (ι.t̂ x)))
                                        (θkγ kx)))
        βA .t̂ x β .tyβ γ kγ kx with G₀FI.[]≡tʰ→return
            {ι.θ (I.t̂ x)}
            {ι.θ γ}
            (θka kγ kx)
            ((≡→≈ (θka kγ kx) .∧e₁ .∧e₂
              (∧i tt* , G₀FI.con↓ (ι.θ γ) (θkγ kγ))) .∧e₂)
        ... | γ₀ , a₀ , qeq =
          let q = trans (sym (ι.t̂ x)) (qeq .∧e₁)
              z = map-return-inj G₀FI.t̂ (ι.θ x) (G₀FI.ty γ₀ a₀) q
          in ⊥e* (G₀FI.encode (z .snd))

        βA .kt̂ x β kx = refl
        βA .∙ .conβ _ = ι.∙
        βA .∙ .tyβ γ kγ kx = ⊥e (G₀FI.cʰ≢tʰ {ι.θ γ} q)
          where
          q : G₀FI.cʰ ≡ G₀FI.tʰ (ι.θ γ)
          q = trans (sym G₀FI.[∙]≡ĉ)
                    (trans (cong G₀FI.[_] (sym ι.∙))
                            (θka kγ kx))
        βA .k∙ = refl

            -- ▷⁻γ : ∀ a
            --   → I.[ I.▷ x a ] ≡ I.ĉ
            --   → I.[ x ] ≡ I.ĉ
            -- ▷-a : ∀ γ
            --   → I.[ I.▷ γ x ] ≡ I.ĉ
            --   → I.[ x ] ≡ I.t̂ γ
        βA .▷ γ a βγ βa .▷⁻γ a' k▷ = {!!}
        βA .▷ γ a βγ βa .conβ k▷ =
          ι.θ (I.▷ γ a)
            ≡⟨ ι.▷ γ a kγ' (βa.▷-a γ k▷) ⟩
          G₀FI.▷ (ι.θ γ) (ι.θ a)
            ≡⟨ cong₂ G₀FI.▷ γ-con a-ty ⟩
          G₀FI.▷ (return (G₀.con (γ , kγ')))
                  (return (G₀.ty (γ , kγ') (a , ka')))
            ≡⟨ G₀FI.▷≡return
                  (G₀.con (γ , kγ'))
                  (G₀.ty (γ , kγ') (a , ka'))
                  refl refl ⟩
          return (G₀.con (I.▷ γ a , _)) ∎
          where
          module βγ = Beta βγ
          module βa = Beta βa
          kγ' : I.[ γ ] ≡ I.ĉ
          kγ' = βγ.▷⁻γ a k▷
          γ-con : ι.θ γ ≡ return (G₀.con (γ , _))
          γ-con = βγ.conβ (βγ.▷⁻γ a k▷)
          ka' : I.[ a ] ≡ I.t̂ γ
          ka' = βa.▷-a γ k▷
          a-ty : ι.θ a ≡ return (G₀.ty (γ , _) (a , _))
          a-ty = βa.tyβ γ kγ' (βa.▷-a γ k▷)
        βA .▷ γ a kγ ka .tyβ = {!!}
        βA .k▷ γ a γᴰ aᴰ kγ ka = refl
        βA .u = {!!}
        βA .ku γ γᴰ kγ = refl
        βA .π = {!!}
        βA .kπ γ a b γᴰ aᴰ bᴰ kγ ka kb = refl
        βA .σ = {!!}
        βA .kσ γ a b γᴰ aᴰ bᴰ kγ ka kb = refl
        βA .σ▷ γ a b γᴰ aᴰ bᴰ kγ ka kb = refl
        βA .σπ γ a b c γᴰ aᴰ bᴰ cᴰ kγ ka kb kc = {!!}
        -}
    con≡₀ γ kγ (G₀.ty δ a , pγ!) = ⊥e (G₀FI.ĉ≢t̂ (sym q))
      where
      q : G₀FI.t̂ (G₀FI.con δ) ≡ G₀FI.ĉ
      q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
    con≡₀ γ kγ (G₀.k̂ , pγ!) = ⊥e (G₀FI.k̂≢ĉ q)
      where
      q : G₀FI.k̂ ≡ G₀FI.ĉ
      q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
    con≡₀ γ kγ (G₀.ĉ , pγ!) = ⊥e (G₀FI.k̂≢ĉ q)
      where
      q : G₀FI.k̂ ≡ G₀FI.ĉ
      q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
    con≡₀ γ kγ (G₀.t̂ δ , pγ!) = ⊥e (G₀FI.k̂≢ĉ q)
      where
      q : G₀FI.k̂ ≡ G₀FI.ĉ
      q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
    con≡ : (γ : FGFI.Con) → Fι.conᴿ (εFI.conᴿ γ) ≡ γ
    con≡ (γ , kγ) = ΣP≡ _ _ (con≡₀ γ kγ (inspect (γ ! G₀FI.con↓ γ kγ)))
    ty≡ : (γ : FGFI.Con) (a : FGFI.Ty γ)
        → subst FGFI.Ty (con≡ γ) (Fι.tyᴿ (εFI.conᴿ γ) (εFI.tyᴿ γ a)) ≡ a

  ε∘Fι≡id : ε FI D.∘ Fι D.≈ D.id
  ε∘Fι≡id = {!D.mk≈ con≡ ty≡!}
    where
    εFI : D.Hom FGFI FI
    εFI = ε FI
    module εFI = ε FI
    module εFI₀ = D.Hom εFI
    con≡₀ : (γ : I.CT)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → εFI.conᴿ (Fι.conᴿ (γ , kγ)) .fst ≡ γ
    con≡₀ γ kγ = 
      εFI.conᴿ (Fι.conᴿ (γ , kγ)) .fst
        ≡⟨ {!!} ⟩
      εFI.conᴿ (ι.θ γ , {!!}) .fst
        ≡⟨ {!!} ⟩
      εFI.conᴿ (ι.θ γ , {!!}) .fst
        ≡⟨ {!!} ⟩
      γ ∎
    con≡ : (γ : FI.Con) → εFI.conᴿ (Fι.conᴿ γ) ≡ γ
    con≡ (γ , kγ) = ΣP≡ _ _ {!!}
    ty≡ : (γ : FI.Con) (a : FI.Ty γ)
        → subst FI.Ty (con≡ γ) (εFI.tyᴿ (Fι.conᴿ γ) (Fι.tyᴿ γ a)) ≡ a
    con≡₀ : (γ : FI.Con) → ι.θ (γ .fst) ≡ return (G₀FI.con γ)
    con≡₀ (γ , kγ) = 
      ι.θ γ
        ≡⟨ {!!} ⟩
      return (G₀FI.con (γ , kγ)) ∎
    con≡ : (γ : FI.Con) → Fι.conᴿ γ ≡ εFI.conᴿ γ
    con≡ γ = ΣP≡ _ _ (con≡₀ γ)
    ty≡ : (γ : FI.Con) (a : FI.Ty γ)
        → subst FGFI.Ty (con≡ γ) (Fι.tyᴿ γ a)
        ≡ ε⁻FI.tyᴿ γ a

  Fι≡ε⁻ : Fι D.≈ ε⁻ FI 
  Fι≡ε⁻ = D.mk≈ con≡ ty≡
    where
    ε⁻FI : D.Hom FI FGFI
    ε⁻FI = ε⁻ FI
    module ε⁻FI = ε⁻ FI
    module ε⁻FI₀ = D.Hom ε⁻FI
    con≡₀ : (γ : FI.Con) → ι.θ (γ .fst) ≡ return (G₀FI.con γ)
    con≡₀ (γ , kγ) = 
      ι.θ γ
        ≡⟨ {!!} ⟩
      return (G₀FI.con (γ , kγ)) ∎
    con≡ : (γ : FI.Con) → Fι.conᴿ γ ≡ ε⁻FI.conᴿ γ
    con≡ γ = ΣP≡ _ _ (con≡₀ γ)
    ty≡ : (γ : FI.Con) (a : FI.Ty γ)
        → subst FGFI.Ty (con≡ γ) (Fι.tyᴿ γ a)
        ≡ ε⁻FI.tyᴿ γ a

  g : D.Hom FI FGA
  g = ε⁻ A D.∘ f
  module f = D.Hom f
  module g = D.Hom g

  η : W.Hom I GA
  η = G₁ (ε A) W.∘ G₁ g W.∘ ι
  module η = W.Hom η
  open η using (θ)

  Fη : D.Hom (F₀ I) (F₀ (G₀ A))
  Fη = F₁ η
  module Fη = F₁ η



  con↓ : ∀ γ
    → (kγ : I.[ γ ] ≡ I.ĉ)
    → θ γ ↓
  con↓ γ kγ = G₀A.con↓ (θ γ) (θkγ kγ)

  getCon : ∀ γ
    → (kγ : I.[ γ ] ≡ I.ĉ)
    → G₀A.Atom
  getCon γ kγ = G₀A.getConAtom (θ γ) (θkγ kγ)

  ty↓ : ∀ γ a
    → (kγ : I.[ γ ] ≡ I.ĉ)
    → (ka : I.[ a ] ≡ I.t̂ γ)
    → θ a ↓
  ty↓ γ a kγ ka =
    G₀A.ty↓ (θ γ) (θ a) (θkγ kγ) (θka kγ ka )

  η : D.Hom (F₀ I) A
  η .D.conᴿ (γ , kγ) =
    {!!}
    where
    cd₁ = con↓ γ
  η .D.tyᴿ (γ , kγ) (a , ka) =
    {!!} 
  η .D.∙ᴿ = {!!}
  η .D.▷ᴿ = {!!}
  η .D.uᴿ = {!!}
  η .D.πᴿ = {!!}
  η .D.σᴿ = {!!}

  η↑ : D.Hom (F₀ I) A↑
  η↑ = D.Lift⇒ ℓA' A D.∘ η

  τ : W.Hom {ℓA = lsuc (lsuc ℓA)} (G₀ (F₀ I)) (G₀ A↑)
  τ = G₁ {!!}

  beta : F₁ r D.≈ f
  beta =
    D.mk≈ {!con≡!} {!ty≡!}
    where

    conEq : (γ : I.CT) → I.[ γ ] ≡ I.ĉ → G₀A.[ θ γ ] ≡ G₀A.cʰ
    conEq γ kγ =
      G₀A.[ θ γ ]
        ≡⟨ sym (r.[ γ ]) ⟩
      θ I.[ γ ]
        ≡⟨ cong θ kγ ⟩
      θ I.ĉ
        ≡⟨ r.ĉ ⟩
      G₀A.cʰ ∎
      where open ≡-Reasoning

    conDef : (γ : I.CT) → I.[ γ ] ≡ I.ĉ → θ γ ↓
    conDef γ kγ = (≡→≈ (conEq γ kγ) .∧e₁ .∧e₂ tt*) .∧e₂

    tyEq : (γ a : I.CT)
      → I.[ γ ] ≡ I.ĉ
      → I.[ a ] ≡ I.t̂ γ
      → G₀A.[ θ a ] ≡ G₀A.tʰ (θ γ)
    tyEq γ a kγ ka =
      G₀A.[ θ a ]
        ≡⟨ sym (r.[ a ]) ⟩
      θ I.[ a ]
        ≡⟨ cong θ ka ⟩
      θ (I.t̂ γ)
        ≡⟨ r.t̂ γ ⟩
      G₀A.tʰ (θ γ) ∎
      where open ≡-Reasoning

    tyDef : (γ a : I.CT)
      → I.[ γ ] ≡ I.ĉ
      → I.[ a ] ≡ I.t̂ γ
      → θ a ↓
    tyDef γ a kγ ka =
      (≡→≈ (tyEq γ a kγ ka) .∧e₁ .∧e₂ (∧i tt* , conDef γ kγ)) .∧e₂

    conRet : (γ : I.CT)
      → I.[ γ ] ≡ I.ĉ
      → ΣP A.Con λ γ₀ → θ γ ≡ return (G₀A.con γ₀)
    conRet γ kγ = G₀A.[]≡cʰ→return (conEq γ kγ)

    tyRet : (γ a : I.CT)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → Σ A.Con λ γ₀
      → ΣP (A.Ty γ₀) λ a₀
      → θ a ≡ return (G₀A.ty γ₀ a₀)
      ∧ θ γ ≡ return (G₀A.con γ₀)
    tyRet γ a kγ ka = G₀A.[]≡tʰ→return (tyEq γ a kγ ka) (tyDef γ a kγ ka)

    ▷-inv : (γ a : I.CT)
      → (kγ : I.[ γ ] ≡ I.ĉ)
      → (ka : I.[ a ] ≡ I.t̂ γ)
      → (▷↓ : θ (I.▷ γ a) ↓)
      → θ γ ↓
      ∧ θ a ↓
    ▷-inv γ a kγ ka ▷↓ = ∧i γ↓ , a↓
      where
      ▷↓' : G₀A.▷ (θ γ) (θ a) ↓
      ▷↓' = substp (_↓) (r.▷ γ a kγ ka) ▷↓
      γ↓ : θ γ ↓
      γ↓ = G₀A.▷⁻-γ (θ γ) (θ a) ▷↓'
      a↓ : θ a ↓
      a↓ = G₀A.▷⁻-a (θ γ) (θ a) ▷↓'

    record P (x : I.CT) : Prop (lsuc ℓA) where
      field
        Conβ :
          (kx : I.[ x ] ≡ I.ĉ)
          → θ x ≡ f.conᴿ (x , kx) .fst
        Tyβ : 
          (γ : I.CT)
          → (kγ : I.[ γ ] ≡ I.ĉ)
          → (kx : I.[ x ] ≡ I.t̂ γ)
          → θ x ≡ f.tyᴿ (γ , kγ) (x , kx) .fst
        ▷-con-γ : ∀ γ a
          → x ≡ I.▷ γ a
          → I.[ I.▷ γ a ] ≡ I.ĉ
          → I.[ γ ] ≡ I.ĉ
        ▷-con-a : ∀ γ a
          → x ≡ I.▷ γ a
          → I.[ I.▷ γ a ] ≡ I.ĉ
          → I.[ a ] ≡ I.t̂ γ
        ▷-ty-absurd : ∀ γ a δ
          → x ≡ I.▷ γ a
          → (kγ : I.[ γ ] ≡ I.ĉ)
          → (ka : I.[ a ] ≡ I.t̂ δ)
          → I.[ I.▷ γ a ] ≡ I.t̂ δ
          → ⊥
        u-con-absurd : ∀ {γ}
          → I.[ I.u γ ] ≡ I.ĉ
          → ⊥
        u-ty-inv : ∀ {γ γ'}
          → I.[ I.u γ ] ≡ I.t̂ γ'
          → I.[ γ ] ≡ I.ĉ ∧ᵖ λ _ → γ' ≡ γ

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
      CT = ΣP I.CT P

      open P

      [_] : CT → CT
      [ x , px ] = I.[ x ] , p
        where
        p : P I.[ x ]
        p .Conβ kx = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} q)
          where
          q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
          q = trans (cong G₀A.[_] (sym r.[ x ])) (conEq (I.[ x ]) kx)
        p .Tyβ γ kγ kx = ⊥e (G₀A.[[x]]≢tʰ {θ x} {θ γ} x↓ q)
          where
          γ↓ : θ γ ↓
          γ↓ = conDef γ kγ

          q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.tʰ (θ γ)
          q = trans (cong G₀A.[_] (sym r.[ x ])) (tyEq γ (I.[ x ]) kγ kx)

          q≈ : G₀A.[ G₀A.[ θ x ] ] ≈ G₀A.tʰ (θ γ)
          q≈ = ≡→≈ q

          x↓ : θ x ↓
          x↓ = (q≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂
        p .▷-con-γ γ a [x]≡▷ k▷ = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} q)
          where
          kx : I.[ I.[ x ] ] ≡ I.ĉ
          kx = trans (cong I.[_] [x]≡▷) k▷
          q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
          q = trans (cong G₀A.[_] (sym r.[ x ]))
                      (conEq (I.[ x ]) kx)
        p .▷-con-a γ a [x]≡▷ k▷ = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} q)
          where
          kx : I.[ I.[ x ] ] ≡ I.ĉ
          kx = trans (cong I.[_] [x]≡▷) k▷
          q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
          q = trans (cong G₀A.[_] (sym r.[ x ]))
                      (conEq (I.[ x ]) kx)
        p .▷-ty-absurd = {!!}
        p .u-con-absurd = P.u-con-absurd px
        p .u-ty-inv = P.u-ty-inv px

      k̂ : CT
      k̂ = I.k̂ , p
        where
        p : P I.k̂
        p .Conβ kk̂ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
          where
          k̂≡ĉ : GA.k̂ ≡ GA.ĉ
          k̂≡ĉ =
            trans
              (sym GA.kk̂)
              (trans (cong GA.[_] (sym r.k̂))
                        (conEq I.k̂ kk̂))
        p .Tyβ γ kγ ka = ⊥e (G₀A.[kʰ]≢tʰ {x* = θ γ} q)
          where
          q : GA.[ GA.k̂ ] ≡ GA.t̂ (θ γ)
          q = trans (cong GA.[_] (sym r.k̂))
                        (tyEq γ I.k̂ kγ ka)
        p .▷-con-γ γ a x≡▷ k▷ = ⊥e (G₀A.[kʰ]≢cʰ {!!})
          where
          q : GA.[ GA.k̂ ] ≡ GA.ĉ
          q = trans (cong GA.[_] (sym r.k̂))
                        (conEq I.k̂ {!!})
        p .▷-con-a γ a x x₁ = {!!}
        p .▷-ty-absurd = {!!}
        p .u-con-absurd = {!!}
        p .u-ty-inv = {!!}

      kk̂ : [ k̂ ] ≡ k̂
      kk̂ = ΣP≡ _ _ I.kk̂

      ĉ : CT
      ĉ = I.ĉ , p
        where
        p : P I.ĉ
        p .Conβ kĉ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
          where
          k̂≡ĉ : GA.k̂ ≡ GA.ĉ
          k̂≡ĉ =
            trans
              (sym GA.kĉ)
              (trans (cong GA.[_] (sym r.ĉ))
                        (conEq I.ĉ kĉ))
        p .Tyβ γ kγ ka = ⊥e (G₀A.[cʰ]≢tʰ {x* = θ γ} q)
          where
          q : GA.[ GA.ĉ ] ≡ GA.t̂ (θ γ)
          q = trans (cong GA.[_] (sym r.ĉ))
                        (tyEq γ I.ĉ kγ ka)
        p .▷-con-γ = {!!}
        p .▷-con-a = {!!}
        p .▷-ty-absurd = {!!}
        p .u-con-absurd = {!!}
        p .u-ty-inv = {!!}

      kĉ : [ ĉ ] ≡ k̂
      kĉ = ΣP≡ _ _ I.kĉ

      t̂ : CT → CT
      t̂ (x , ∧i cx , tx) = I.t̂ x , ∧i ct , tyt
        where
        open ≡-Reasoning
        ct : Conβ (I.t̂ x)
        ct kx = ⊥e (G₀A.[tʰ]≢cʰ {x* = θ x} p)
          where
          p : GA.[ GA.t̂ (θ x) ] ≡ GA.ĉ
          p =
            GA.[ GA.t̂ (θ x) ]
              ≡⟨ cong GA.[_] (sym (r.t̂ x)) ⟩
            GA.[ θ (I.t̂ x) ]
              ≡⟨ sym (r.[ I.t̂ x ]) ⟩
            θ I.[ I.t̂ x ]
              ≡⟨ cong θ kx ⟩
            θ I.ĉ
              ≡⟨ r.ĉ ⟩
            GA.ĉ ∎
        tyt : Tyβ (I.t̂ x)
        tyt γ kγ ka with tyRet γ (I.t̂ x) kγ ka
        ... | γ₀ , a₀ , qeq = ⊥e* (G₀A.encode (u .snd))
          where
          p : G₀A.tʰ (θ x) ≡ return (G₀A.ty γ₀ a₀)
          p = trans (sym (r.t̂ x)) (qeq .∧e₁)
          u : ΣP G₀A.Atom λ z → G₀A.t̂ z ≡ G₀A.ty γ₀ a₀
          u = map-return-inj G₀A.t̂ (θ x) (G₀A.ty γ₀ a₀) p

      kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
      kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (I.kt̂ x (cong fst kγ))

      ∙ : CT
      ∙ = I.∙ , ∧i c∙ , t∙
        where
        c∙ : Conβ I.∙
        c∙ k∙ =
          θ I.∙
            ≡⟨ r.∙ ⟩
          GA.∙
            ≡⟨ sym (cong fst f.∙ᴿ) ⟩
          f.conᴿ (I.∙ , k∙) .fst ∎
          where open ≡-Reasoning
        t∙ : Tyβ I.∙
        t∙ γ kγ ka = ⊥e (G₀A.cʰ≢tʰ {x = θ γ} p)
          where
          p : GA.ĉ ≡ GA.t̂ (θ γ)
          p =
            trans
              (sym GA.k∙)
              (trans (cong GA.[_] (sym r.∙))
                        (tyEq γ I.∙ kγ ka))

      k∙ : [ ∙ ] ≡ ĉ
      k∙ = ΣP≡ _ _ I.k∙

      ▷ : CT → CT → CT
      ▷ (γ , pγ) (a , pa) =
        I.▷ γ a , ∧i c▷ , t▷
        where
        c▷ : Conβ (I.▷ γ a)
        c▷ kx =
          θ (I.▷ γ a)
            ≡⟨ r.▷ γ a kγ ka ⟩
          GA.▷ (θ γ) (θ a)
            ≡⟨ cong₂ GA.▷ (pγ .∧e₁ kγ) (pa .∧e₂ γ kγ ka) ⟩
          GA.▷
            (f.conᴿ (γ , kγ) .fst)
            (f.tyᴿ (γ , kγ) (a , ka) .fst)
            ≡⟨ sym (cong fst (f.▷ᴿ (γ , kγ) (a , ka))) ⟩
          f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
            ≡⟨ p▷ ⟩
          f.conᴿ (I.▷ γ a , kx) .fst ∎
          where
          open ≡-Reasoning
          kγa : I.[ γ ] ≡ I.ĉ ∧ᵖ λ kγ
            → I.[ a ] ≡ I.t̂ γ
          kγa = {!▷-con-inv kx!}
          kγ = kγa .∧e₁
          ka = kγa .∧e₂
          p▷ : f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
              ≡ f.conᴿ (I.▷ γ a , kx) .fst
          p▷ = cong fst (cong f.conᴿ (ΣP≡ _ _ refl))
        t▷ : Tyβ (I.▷ γ a)
        t▷ γ kγ ka = ⊥e {!∀ δ → {!▷-ty-absurd γ kγ a {!ka!} δ!}!}

      k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
      k▷ (γ , pγ) (a , pa) kγ ka = ΣP≡ _ _ (I.k▷ γ a (cong fst kγ) (cong fst ka))

      u : CT → CT
      u (γ , pγ) =
        I.u γ , ∧i cu , tu
        where
        cu : Conβ (I.u γ)
        cu = {!!} 
        tu : Tyβ (I.u γ)
        tu γ kγ ka = {!!}

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

    allP : (x : I.CT) → P x
    allP x = {!!}

    con≡ : (γ : D.Con (F₀ I)) → F₁.conᴿ (invFG f) γ ≡ f.conᴿ γ
    con≡ (γ , kγ) =
      ΣP≡ _ _ (allP γ .∧e₁ kγ)

    ty≡ : (γ : D.Con (F₀ I)) (a : F₀ I .D.Ty γ) →
            subst (D.Ty (F₀ (G₀ A))) (con≡ γ) (D.tyᴿ (F₁ (invFG f)) γ a) ≡
            f.tyᴿ γ a
    ty≡ (γ , kγ) (a , ka) = {!!}

      [_] : CT → CT
      [ x , ∧i cx , cy ] = I.[ x ] , ∧i c[x] , t[x]
        where
        c[x] : Conβ I.[ x ]
        c[x] kx = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} p)
          where
          p : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
          p = trans (cong G₀A.[_] (sym r.[ x ])) (conEq (I.[ x ]) kx)
        t[x] : Tyβ I.[ x ]
        t[x] γ kγ ka =
          ⊥e (G₀A.[[x]]≢tʰ
            {x* = θ x}
            {y* = θ γ}
            x↓
            p)
          where
          γ↓ : θ γ ↓
          γ↓ = conDef γ kγ

          p : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.tʰ (θ γ)
          p = trans (cong G₀A.[_] (sym r.[ x ])) (tyEq γ (I.[ x ]) kγ ka)

          p≈ : G₀A.[ G₀A.[ θ x ] ] ≈ G₀A.tʰ (θ γ)
          p≈ = ≡→≈ p

          x↓ : θ x ↓
          x↓ = (p≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂

      k̂ : CT
      k̂ = I.k̂ , ∧i ck̂ , tk̂
        where
        ck̂ : Conβ Fr.A.k̂
        ck̂ kk̂ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
          where
          k̂≡ĉ : GA.k̂ ≡ GA.ĉ
          k̂≡ĉ =
            trans
              (sym GA.kk̂)
              (trans (cong GA.[_] (sym r.k̂))
                        (conEq I.k̂ kk̂))
        tk̂ : Tyβ Fr.A.k̂
        tk̂ γ kγ ka = ⊥e (G₀A.[kʰ]≢tʰ {x* = θ γ} p)
          where
          p : GA.[ GA.k̂ ] ≡ GA.t̂ (θ γ)
          p = trans (cong GA.[_] (sym r.k̂)) (tyEq γ I.k̂ kγ ka)

      kk̂ : [ k̂ ] ≡ k̂
      kk̂ = ΣP≡ _ _ I.kk̂

      ĉ : CT
      ĉ = I.ĉ , ∧i cĉ , tĉ
        where
        cĉ : Conβ I.ĉ
        cĉ kĉ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
          where
          k̂≡ĉ : GA.k̂ ≡ GA.ĉ
          k̂≡ĉ =
            trans
              (sym GA.kĉ)
              (trans (cong GA.[_] (sym r.ĉ))
                        (conEq I.ĉ kĉ))
        tĉ : Tyβ I.ĉ
        tĉ γ kγ ka = ⊥e (G₀A.[cʰ]≢tʰ {x* = θ γ} p)
          where
          p : GA.[ GA.ĉ ] ≡ GA.t̂ (θ γ)
          p = trans (cong GA.[_] (sym r.ĉ)) (tyEq γ I.ĉ kγ ka)

      kĉ : [ ĉ ] ≡ k̂
      kĉ = ΣP≡ _ _ I.kĉ

      t̂ : CT → CT
      t̂ (x , ∧i cx , tx) = I.t̂ x , ∧i ct , tyt
        where
        open ≡-Reasoning
        ct : Conβ (I.t̂ x)
        ct kx = ⊥e (G₀A.[tʰ]≢cʰ {x* = θ x} p)
          where
          p : GA.[ GA.t̂ (θ x) ] ≡ GA.ĉ
          p =
            GA.[ GA.t̂ (θ x) ]
              ≡⟨ cong GA.[_] (sym (r.t̂ x)) ⟩
            GA.[ θ (I.t̂ x) ]
              ≡⟨ sym (r.[ I.t̂ x ]) ⟩
            θ I.[ I.t̂ x ]
              ≡⟨ cong θ kx ⟩
            θ I.ĉ
              ≡⟨ r.ĉ ⟩
            GA.ĉ ∎
        tyt : Tyβ (I.t̂ x)
        tyt γ kγ ka with tyRet γ (I.t̂ x) kγ ka
        ... | γ₀ , a₀ , qeq = ⊥e* (G₀A.encode (u .snd))
          where
          p : G₀A.tʰ (θ x) ≡ return (G₀A.ty γ₀ a₀)
          p = trans (sym (r.t̂ x)) (qeq .∧e₁)
          u : ΣP G₀A.Atom λ z → G₀A.t̂ z ≡ G₀A.ty γ₀ a₀
          u = map-return-inj G₀A.t̂ (θ x) (G₀A.ty γ₀ a₀) p

      kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
      kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (I.kt̂ x (cong fst kγ))

      ∙ : CT
      ∙ = I.∙ , ∧i c∙ , t∙
        where
        c∙ : Conβ I.∙
        c∙ k∙ =
          θ I.∙
            ≡⟨ r.∙ ⟩
          GA.∙
            ≡⟨ sym (cong fst f.∙ᴿ) ⟩
          f.conᴿ (I.∙ , k∙) .fst ∎
          where open ≡-Reasoning
        t∙ : Tyβ I.∙
        t∙ γ kγ ka = ⊥e (G₀A.cʰ≢tʰ {x = θ γ} p)
          where
          p : GA.ĉ ≡ GA.t̂ (θ γ)
          p =
            trans
              (sym GA.k∙)
              (trans (cong GA.[_] (sym r.∙))
                        (tyEq γ I.∙ kγ ka))

      k∙ : [ ∙ ] ≡ ĉ
      k∙ = ΣP≡ _ _ I.k∙

      ▷ : CT → CT → CT
      ▷ (γ , pγ) (a , pa) =
        I.▷ γ a , ∧i c▷ , t▷
        where
        c▷ : Conβ (I.▷ γ a)
        c▷ kx =
          θ (I.▷ γ a)
            ≡⟨ r.▷ γ a kγ ka ⟩
          GA.▷ (θ γ) (θ a)
            ≡⟨ cong₂ GA.▷ (pγ .∧e₁ kγ) (pa .∧e₂ γ kγ ka) ⟩
          GA.▷
            (f.conᴿ (γ , kγ) .fst)
            (f.tyᴿ (γ , kγ) (a , ka) .fst)
            ≡⟨ sym (cong fst (f.▷ᴿ (γ , kγ) (a , ka))) ⟩
          f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
            ≡⟨ p▷ ⟩
          f.conᴿ (I.▷ γ a , kx) .fst ∎
          where
          open ≡-Reasoning
          kγa : I.[ γ ] ≡ I.ĉ ∧ᵖ λ kγ
            → I.[ a ] ≡ I.t̂ γ
          kγa = ▷-con-inv kx
          kγ = kγa .∧e₁
          ka = kγa .∧e₂
          p▷ : f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
              ≡ f.conᴿ (I.▷ γ a , kx) .fst
          p▷ = cong fst (cong f.conᴿ (ΣP≡ _ _ refl))
        t▷ : Tyβ (I.▷ γ a)
        t▷ γ kγ ka = ⊥e {!∀ δ → {!▷-ty-absurd γ kγ a {!ka!} δ!}!}

      k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
      k▷ (γ , pγ) (a , pa) kγ ka = ΣP≡ _ _ (I.k▷ γ a (cong fst kγ) (cong fst ka))

      u : CT → CT
      u (γ , pγ) =
        I.u γ , ∧i cu , tu
        where
        cu : Conβ (I.u γ)
        cu = {!!} 
        tu : Tyβ (I.u γ)
        tu γ kγ ka = {!!}

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

    allP : (x : I.CT) → P x
    allP x = {!!}

    con≡ : (γ : D.Con (F₀ I)) → F₁.conᴿ (invFG f) γ ≡ f.conᴿ γ
    con≡ (γ , kγ) =
      ΣP≡ _ _ (allP γ .∧e₁ kγ)

    ty≡ : (γ : D.Con (F₀ I)) (a : F₀ I .D.Ty γ) →
            subst (D.Ty (F₀ (G₀ A))) (con≡ γ) (D.tyᴿ (F₁ (invFG f)) γ a) ≡
            f.tyᴿ γ a
    ty≡ (γ , kγ) (a , ka) = {!!}

  recUniqueᴰ : {A : D.Algebra ℓA} → (f : D.Hom FI A) → f D.≈ recᴰ A
  recUniqueᴰ {A = A} f = D≈.trans FI A (D≈.sym (F₀ I) A β) η
    where
    module D≈ {ℓA} {ℓB} A B = ≈.Setoid (D.HomSetoid {ℓA} {ℓB} A B)
    module Dᶜ ℓA = Category (D.Cat ℓA)
    module F ℓA = Functor (F ℓA)
    q : D.Hom FI (F₀ (G₀ A))
    q = ε⁻ A D.∘ f
    β : (ε A D.∘ F₁ (invFG q)) D.≈ f
    β =
      ε A D.∘ F₁ (invFG q)
        ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ A)) A {ε A}) (invFG-beta q) ⟩
      ε A D.∘ (ε⁻ A D.∘ f)
        ≈⟨ D≈.refl FI A ⟩
      f ∎
      where
      open ≈.≈syntax {S = D.HomSetoid FI A}
    η : (ε A D.∘ F₁ (invFG q)) D.≈ recᴰ A
    η =
      ε A D.∘ F₁ (invFG q)
        ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ A)) A {ε A})
                      (F.resp (lsuc ℓA) (recUniqueᵂ (invFG q))) ⟩
      ε A D.∘ F₁ (recᵂ (G₀ A)) ∎
      where
      open ≈.≈syntax {S = D.HomSetoid FI A}
-}

      con≡₀' : (γ : I.CT) (kγ : I.[ γ ] ≡ I.ĉ)
        → (kδ : G₀FI.[ return (G₀FI.con (γ , kγ)) ] ≡ G₀FI.cʰ)
        → ι.θ (εFI.conᴿ (return (G₀FI.con (γ , kγ)) , kδ) .fst) ≡ return (G₀FI.con (γ , kγ))
      con≡₀' γ kγ kδ =
        ι.θ (εFI.conᴿ (return (G₀FI.con (γ , kγ)) , kδ) .fst)
          ≡⟨ {!!} ⟩
        ι.θ (εFI.conᴿ (return (G₀FI.con (γ , kγ)) , kδ) .fst)
          ≡⟨ {!!} ⟩
        return (G₀FI.con (γ , kγ)) ∎
      con≡₀ : (γ : GFI.CT) (kγ : GFI.[ γ ] ≡ GFI.ĉ)
        → {γ↓ : γ ↓}
        → Singleton (γ ! γ↓)
        → ι.θ (εFI.conᴿ (γ , kγ) .fst) ≡ γ
      con≡₀ γ kγ {γ↓} (G₀FI.con (δ , kδ) , pγ!) = -- trans (trans (cong ι.θ {!!}) (mk≡↓ {x* = ι.θ {!!}} {!p!} γ↓ {!!})) refl
        ι.θ (εFI.conᴿ (γ , kγ) .fst)
          ≡⟨ cong
               (λ ○ → ι.θ (fst (εFI.conᴿ ○)))
               {γ , kγ} {return (G₀FI.con (δ , kδ)) , kγ''}
               (ΣP≡ _ _ (mk≡↓ γ↓ tt* (sym pγ!))) ⟩
        ι.θ (εFI.conᴿ (return (G₀FI.con (δ , kδ)) , kγ'') .fst)
          ≡⟨ s ⟩
        return (G₀FI.con (δ , kδ))
          ≡⟨ mk≡↓ tt* γ↓ pγ! ⟩
        γ ∎
        where
        kγ'' : G₀FI.[ return (G₀FI.con (δ , kδ)) ] ≡ G₀FI.cʰ
        kγ'' = trans (map-beta G₀FI.[_]₀ (G₀FI.con (δ , kδ))) refl
        s : ι.θ (εFI.conᴿ (return (G₀FI.con (δ , kδ)) , kγ'') .fst)
          ≡ return (G₀FI.con (δ , kδ))
        s = con≡₀' δ kδ kγ''
