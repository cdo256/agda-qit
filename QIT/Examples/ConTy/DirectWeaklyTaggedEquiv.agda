{-# OPTIONS --type-in-type #-}
{-
This module relates the direct and weakly tagged presentations of ConTy.

The direct presentation D has two sorts:

  Con : Set
  Ty  : Con → Set

whereas the weakly tagged presentation W has a single sort CT, together
with atoms and kinding operations.

We construct functors

  F : W → D
  G : D → W

and use them to transfer initiality from W to D.

The functor F
=============

Given a weakly tagged algebra A, the direct algebra F A is obtained by
taking dependent sums of terms together with proofs of their kinds:

  F A .Con =
    ΣP A.CT λ γ →
      A.[ γ ] ≡ A.ĉ

  F A .Ty (γ , kγ) =
    ΣP A.CT λ a →
      A.[ a ] ≡ A.t̂ γ

The action of F on morphisms maps the underlying CT terms and transports
the kinding proofs using the homomorphism equations.

The functor G
=============

Given a direct algebra A, define the type of atoms by

  data Atom : Set ℓA where
    con : A.Con → Atom
    ty  : (γ : A.Con) → A.Ty γ → Atom
    k̂   : Atom
    ĉ   : Atom
    t̂   : Atom → Atom

The carrier of G A is the propositional lifting of Atom:

  CT = PropLift ℓA Atom

A value

  P ⊢ x : PropLift ℓA Atom

consists of a proposition P specifying when the value is defined and a
function x : P → Atom giving its value whenever P holds.

This is needed because the domain conditions of the weakly tagged
operations need not be decidable. For example, context extension applied
to atoms

  con γ
  ty γ′ a

is valid only when γ ≡ γ′. Equality in an arbitrary QIIT cannot in
general be assumed decidable.

Propositional lifting also gives the required extensional equality:
using propositional and functional extensionality,

  (P ⊢ x) ≡ (Q ⊢ y)

whenever P ⇔ Q and

  ∀ p q → x p ≡ y q.

Thus different derivations of the same partial value are identified.

The action of G on a direct homomorphism maps the Con and Ty data stored
inside atoms and preserves the remaining atom constructors.

The counit isomorphism
======================

For every direct algebra A, there is an isomorphism

  ε A : F (G A) ≅ A.

The forward direction extracts the Con or Ty stored inside an inhabited
atom whose kind is known. The reverse direction packages a direct
context or type as an always-defined atom:

  γ ↦ return (con γ)
  a ↦ return (ty γ a).

These maps are inverse because the direct presentation contains only
genuine contexts and types.

Transferring initiality
=======================

Suppose I is an initial W-algebra. We aim to prove that F I is initial
in D.

For a direct algebra A, define the canonical homomorphism

  r A : D.Hom (F I) A

by

  r A = ε A ∘ F₁ (rec (G A)).

It remains to prove that r A is unique.

Let

  ι : W.Hom I (G (F I))
  ι = rec (G (F I)).

The central coherence equation is the triangle identity

  F₁ ι ∘ ε (F I) ≈ D.id

or, equivalently,

  ε (F I) ∘ F₁ ι ≈ D.id.

This says that ι maps every well-kinded context or type in I to its
canonical inhabited representation in G (F I):

  ι.θ γ ≡ return (con (γ , kγ))

for kγ : I.[ γ ] ≡ I.ĉ, and

  ι.θ a ≡ return (ty (γ , kγ) (a , ka))

for ka : I.[ a ] ≡ I.t̂ γ.

These canonical-form equations are dependent induction principles for
the initial algebra I; they are not merely constructor beta rules for
the recursor. They can be proved using a displayed W-algebra and section
induction.

Now fix

  f : D.Hom (F I) A

and define

  g : D.Hom (F I) (F (G A))
  g = ε⁻¹ A ∘ f

and

  η : W.Hom I (G A)
  η = G₁ g ∘ ι.

Using the triangle identity and naturality of ε, we obtain

  F₁ η ≈ g.

Initiality of I gives

  η ≈ rec (G A),

and hence

  f ≈ ε A ∘ F₁ (rec (G A))
    ≈ r A.

Therefore F I is initial in D.
-}
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
  ; ▷ᴿ = λ _ _ → refl
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

  tyAtom : (γ : DFA.Con) → DFA.Ty γ → G.Atom
  tyAtom (γ , kγ) (a , ka) = a .val (G.ty↓ γ a kγ ka)

  tyAtom-isTy : (γ : DFA.Con) (a : DFA.Ty γ)
    → G.[ tyAtom γ a ]₀ ≡ G.t̂ (conAtom γ)
  tyAtom-isTy (γ , kγ) (a , ka) = G.tyKind γ a kγ ka

  tyᴿ : (γ : DFA.Con) → DFA.Ty γ → DA.Ty (conᴿ γ)
  tyᴿ γ a = G.Ty₀ (conAtom γ) (tyAtom γ a) (conAtom-isCon γ) (tyAtom-isTy γ a)

  u₀ : (γ : G.Atom) (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → G.Ty₀ γ (G.u₀ γ kγ) kγ (G.ku₀ γ kγ) ≡ DA.u (G.Con₀ γ kγ)
  u₀ (G.con γ) refl = refl

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
  open ≡
  module DA = D.Algebra A
  module G = G₀ A
  module DFA = D.Algebra (F₀ (G₀ A))
  module FGA = F₀ (G₀ A)

  ι : G.Atom → G.CT
  ι x = return x

  kcon : (γ : DA.Con) → G.[ ι (G.con γ) ] ≡ G.cʰ
  kcon γ = mk≡↓ (∧i tt* , tt*) tt* refl

  kty : (γ : DA.Con) (a : DA.Ty γ) → G.[ ι (G.ty γ a) ] ≡ G.tʰ (ι (G.con γ))
  kty γ a = G.mkCT≡ (λ p → p) (λ p → p) λ _ _ → refl

  ▷ι : (γ : DA.Con) (a : DA.Ty γ) → G.▷ (ι (G.con γ)) (ι (G.ty γ a)) ≡ ι (G.con (γ DA.▷ a))
  ▷ι γ a = mk≡↓ q tt* refl
    where
    q : G.▷ (ι (G.con γ)) (ι (G.ty γ a)) ↓
    q = ∧i tt* , ∧i tt* , ∧i refl , ∧i refl , tt*

  uι : (γ : DA.Con) → G.u (ι (G.con γ)) ≡ ι (G.ty γ (DA.u γ))
  uι γ = mk≡↓ q tt* refl
    where
    q : G.u (ι (G.con γ)) .Cond
    q = ∧i tt* , ∧i refl , tt*

  πι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.π γ a b))
  πι γ a b = mk≡↓ q tt* refl
    where
    q : G.π (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) .Cond
    q = ∧i tt* , ∧i tt* , ∧i tt* , ∧i refl , ∧i refl , ∧i refl , tt*

  σι : (γ : DA.Con) (a : DA.Ty γ) (b : DA.Ty (γ DA.▷ a))
    → G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) ≡ ι (G.ty γ (DA.σ γ a b))
  σι γ a b = mk≡↓ q tt* refl
    where
    q : G.σ (ι (G.con γ)) (ι (G.ty γ a)) (ι (G.ty (γ DA.▷ a) b)) .Cond
    q = ∧i tt* , ∧i tt* , ∧i tt* , ∧i refl , ∧i refl , ∧i refl , tt*

  conᴿ : DA.Con → DFA.Con
  conᴿ γ = ι (G.con γ) , kcon γ

  tyᴿ : (γ : DA.Con) → DA.Ty γ → DFA.Ty (conᴿ γ)
  tyᴿ γ a = ι (G.ty γ a) , kty γ a

  ∙ᴿ : conᴿ DA.∙ ≡ DFA.∙
  ∙ᴿ = ΣP≡ _ _ refl

  ▷ᴿ : ∀ γ a → conᴿ (γ DA.▷ a) ≡ conᴿ γ DFA.▷ tyᴿ γ a
  ▷ᴿ γ a = ΣP≡ _ _ (sym (▷ι γ a))

  uᴿ : ∀ γ → tyᴿ γ (DA.u γ) ≡ DFA.u (conᴿ γ)
  uᴿ γ = ΣP≡ _ _ (sym (uι γ))

  πᴿ : ∀ γ a b → tyᴿ γ (DA.π γ a b)
    ≡ DFA.π (conᴿ γ) (tyᴿ γ a) (subst DFA.Ty (▷ᴿ γ a) (tyᴿ (γ DA.▷ a) b))
  πᴿ γ a b = ΣP≡ _ _ p
    where
    p = trans (sym (πι γ a b))
        (cong (G.π (ι (G.con γ)) (ι (G.ty γ a)))
                (sym (FGA.Ty-fst (▷ᴿ γ a))))

  σᴿ : ∀ γ a b → tyᴿ γ (DA.σ γ a b)
    ≡ DFA.σ (conᴿ γ) (tyᴿ γ a) (subst DFA.Ty (▷ᴿ γ a) (tyᴿ (γ DA.▷ a) b))
  σᴿ γ a b = ΣP≡ _ _ p
    where
    p = trans (sym (σι γ a b))
        (cong (G.σ (ι (G.con γ)) (ι (G.ty γ a)))
                (sym (FGA.Ty-fst (▷ᴿ γ a))))

εε⁻ : ∀ {ℓA} (A : D.Algebra ℓA) → (ε A D.∘ ε⁻ A) D.≈ D.id
εε⁻ A = D.mk≈ con≡ ty≡
  where
  open ≡
  module A = D.Algebra A
  con≡ : (γ : A.Con) → (ε A D.∘ ε⁻ A) .D.conᴿ γ ≡ γ
  con≡ γ = refl
  ty≡ : (γ : A.Con) (a : A.Ty γ)
      → subst A.Ty (con≡ γ) ((ε A D.∘ ε⁻ A) .D.tyᴿ γ a)
      ≡ a
  ty≡ γ a = refl


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

  inhabited→ι : (x : G.CT) → (p : x .Cond) → x ≡ ι (x .val p)
  inhabited→ι (P ⊢ f) p = G.mkCT≡ (λ _ → tt*) (λ _ → p) (λ q _ → congp f)

  Ty₀-η : (γ a : G.Atom)
    → (kγ : G.[ γ ]₀ ≡ G.ĉ)
    → (ka : G.[ a ]₀ ≡ G.t̂ γ)
    → G.ty (G.Con₀ γ kγ) (G.Ty₀ γ a kγ ka) ≡ a
  Ty₀-η (G.con γ) (G.ty .γ a) refl refl = refl

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
        (sym (inhabited→ι x witness))

  ty≡ : (γ : DFA.Con) (a : DFA.Ty γ)
      → subst DFA.Ty (con≡ γ) (D.tyᴿ (ε⁻ A D.∘ ε A) γ a)
      ≡ D.tyᴿ (D.id {A = F₀ (G₀ A)}) γ a
  ty≡ γ@(x , kx) a@(y , ky) = ΣP≡ _ _ p
    where
    open ≡
    witness : y .Cond
    witness = G.ty↓ x y kx ky
    q : ι (G.ty (ε.conᴿ A γ) (ε.tyᴿ A γ a)) ≡ y
    q =
      trans
        (cong ι
          (Ty₀-η (ε.conAtom A γ) (ε.tyAtom A γ a)
                 (ε.conAtom-isCon A γ) (ε.tyAtom-isTy A γ a)))
        (sym (inhabited→ι y witness))
    p : subst DFA.Ty (con≡ γ) (D.tyᴿ (ε⁻ A D.∘ ε A) γ a) .fst ≡ y
    p = trans (FG.Ty-fst (con≡ γ)) q

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

  open import QIT.Examples.ConTy.InitialWeaklyTagged I recᵂ recUniqueᵂ

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
        → I.[ a ] ≡ I.t̂ γ
        → G₀FI.[ ι.θ a ] ≡ G₀FI.tʰ (ι.θ γ)
    θka {γ} {a} kγ ka =
      G₀FI.[ ι.θ a ]
        ≡⟨ sym ι.[ a ] ⟩
      ι.θ I.[ a ]
        ≡⟨ cong ι.θ ka ⟩
      ι.θ (I.t̂ γ)
        ≡⟨ ι.t̂ γ ⟩
      G₀FI.tʰ (ι.θ γ) ∎

    Fι∘ε≡id : Fι D.∘ ε FI D.≈ D.id
    Fι∘ε≡id = D.mk≈ {!con≡!} {!ty≡!}
      where
      εFI : D.Hom FGFI FI
      εFI = ε FI
      module εFI = ε FI
      module εFI₀ = D.Hom εFI
      con≡₀ : (γ : GFI.CT) (kγ : GFI.[ γ ] ≡ GFI.ĉ)
        → ι.θ (εFI.conᴿ (γ , kγ) .fst) ≡ γ
      con≡₀ γ kγ with inspect (γ ! G₀FI.con↓ γ kγ)
      ... | G₀.con (δ , kδ) , pγ! = {!!}
        where
        module Beta where
          record Beta (x : I.CT) : Set _ where
            field
              conβ : (kx : I.[ x ] ≡ I.ĉ)
                → ι.θ x ≡ return (G₀.con (x , kx))

              tyβ : ∀ γ
                → (kγ : I.[ γ ] ≡ I.ĉ)
                → (kx : I.[ x ] ≡ I.t̂ γ)
                → ι.θ x
                ≡ return (G₀.ty (γ , kγ) (x , kx))

          open DispAlgebra
          open Beta
          βA : DispAlgebra ℓA'
          βA .CT = Beta
          βA .[] x β .conβ kx = ⊥e (G₀FI.[[x]]≢cʰ {ι.θ x} q)
            where
            q : G₀FI.[ G₀FI.[ ι.θ x ] ] ≡ G₀FI.cʰ
            q = trans (cong G₀FI.[_] (sym ι.[ x ])) (θkγ kx)
          βA .[] x β .tyβ γ kγ k[x] =
            ⊥e (G₀FI.[[x]]≢tʰ {ι.θ x} {ι.θ γ} θx↓ q)
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
          βA .kk̂ = {!!}
          βA .ĉ .conβ kx = ⊥e (G₀FI.kʰ≢cʰ q)
            where
            q : G₀FI.kʰ ≡ G₀FI.cʰ
            q = trans (sym G₀FI.kĉ) (trans (cong G₀FI.[_] (sym ι.ĉ)) (θkγ kx))
          βA .ĉ .tyβ γ kγ kx = ⊥e (G₀FI.[cʰ]≢tʰ {x* = ι.θ γ} q)
            where
            q : G₀FI.[ G₀FI.cʰ ] ≡ G₀FI.tʰ (ι.θ γ)
            q = trans (cong G₀FI.[_] (sym ι.ĉ)) (θka kγ kx)
          βA .kĉ = {!!}
          βA .t̂ x β = p
            where
            tyt : ∀ γ
              → (kγ : I.[ γ ] ≡ I.ĉ)
              → (kx : I.[ I.t̂ x ] ≡ I.t̂ γ)
              → ι.θ (I.t̂ x) ≡ return (G₀.ty (γ , kγ) (I.t̂ x , kx))
            tyt γ kγ kx with G₀FI.[]≡tʰ→return
              {ι.θ (I.t̂ x)}
              {ι.θ γ}
              (θka kγ kx)
              ((≡→≈ (θka kγ kx) .∧e₁ .∧e₂
                (∧i tt* , G₀FI.con↓ (ι.θ γ) (θkγ kγ))) .∧e₂)
            ... | γ₀ , a₀ , qeq =
              let q = trans (sym (ι.t̂ x)) (qeq .∧e₁)
                  z = map-return-inj G₀FI.t̂ (ι.θ x) (G₀FI.ty γ₀ a₀) q
              in ⊥e* (G₀FI.encode (z .snd))

            p : Beta (I.t̂ x)
            p = record
              { conβ = λ kx → ⊥e (G₀FI.[tʰ]≢cʰ {x* = ι.θ x}
                                   (trans (cong G₀FI.[_] (sym (ι.t̂ x)))
                                          (θkγ kx)))
              ; tyβ = λ γ kγ kx → tyt γ kγ kx
              }

          βA .kt̂ x β kx = {!!}
          βA .∙ .conβ _ = ι.∙
          βA .∙ .tyβ γ kγ kx = ⊥e {!G₀FI.[∙]≢t̂ kx!}
          βA .k∙ = {!!}
          -- = ⊥e (G₀FI.kʰ≢cʰ (mk≡↓ tt* tt* {!!}))
          βA .▷ = {!!}
          βA .k▷ = {!!}
          βA .u = {!!}
          βA .ku = {!!}
          βA .π = {!!}
          βA .kπ = {!!}
          βA .σ = {!!}
          βA .kσ = {!!}
          βA .σ▷ = {!!}
          βA .σπ = {!!}
      ... | G₀.ty δ a , pγ! = ⊥e (G₀FI.ĉ≢t̂ (sym q))
        where
        q : G₀FI.t̂ (G₀FI.con δ) ≡ G₀FI.ĉ
        q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
      ... | G₀.k̂ , pγ! = ⊥e (G₀FI.k̂≢ĉ q)
        where
        q : G₀FI.k̂ ≡ G₀FI.ĉ
        q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
      ... | G₀.ĉ , pγ! = ⊥e (G₀FI.k̂≢ĉ q)
        where
        q : G₀FI.k̂ ≡ G₀FI.ĉ
        q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
      ... | G₀.t̂ δ , pγ! = ⊥e (G₀FI.k̂≢ĉ q)
        where
        q : G₀FI.k̂ ≡ G₀FI.ĉ
        q = trans (cong G₀FI.[_]₀ pγ!) (G₀FI.conKind γ kγ)
      con≡ : (γ : FGFI.Con) → Fι.conᴿ (εFI.conᴿ γ) ≡ γ
      con≡ (γ , kγ) = ΣP≡ _ _ (con≡₀ γ kγ)
    --   ty≡ : (γ : FI.Con) (a : FI.Ty γ)
    --       → subst FI.Ty (con≡ γ) (Fι.tyᴿ (εFI.conᴿ γ) (εFI.tyᴿ γ a)) ≡ a

    -- ε∘Fι≡id : ε FI D.∘ Fι D.≈ D.id
    -- ε∘Fι≡id = {!D.mk≈ con≡ ty≡!}
    --   where
    --   εFI : D.Hom FGFI FI
    --   εFI = ε FI
    --   module εFI = ε FI
    --   module εFI₀ = D.Hom εFI
    --   con≡₀ : (γ : I.CT)
    --     → (kγ : I.[ γ ] ≡ I.ĉ)
    --     → εFI.conᴿ (Fι.conᴿ (γ , kγ)) .fst ≡ γ
    --   con≡₀ γ kγ = 
    --     εFI.conᴿ (Fι.conᴿ (γ , kγ)) .fst
    --       ≡⟨ {!!} ⟩
    --     εFI.conᴿ (ι.θ γ , {!!}) .fst
    --       ≡⟨ {!!} ⟩
    --     εFI.conᴿ (ι.θ γ , {!!}) .fst
    --       ≡⟨ {!!} ⟩
    --     γ ∎
    --   con≡ : (γ : FI.Con) → εFI.conᴿ (Fι.conᴿ γ) ≡ γ
    --   con≡ (γ , kγ) = ΣP≡ _ _ {!!}
    --   ty≡ : (γ : FI.Con) (a : FI.Ty γ)
    --       → subst FI.Ty (con≡ γ) (εFI.tyᴿ (Fι.conᴿ γ) (Fι.tyᴿ γ a)) ≡ a
    -- --   con≡₀ : (γ : FI.Con) → ι.θ (γ .fst) ≡ return (G₀FI.con γ)
    -- --   con≡₀ (γ , kγ) = 
    -- --     ι.θ γ
    -- --       ≡⟨ {!!} ⟩
    -- --     return (G₀FI.con (γ , kγ)) ∎
    -- --   con≡ : (γ : FI.Con) → Fι.conᴿ γ ≡ εFI.conᴿ γ
    -- --   con≡ γ = ΣP≡ _ _ (con≡₀ γ)
    -- --   ty≡ : (γ : FI.Con) (a : FI.Ty γ)
    -- --       → subst FGFI.Ty (con≡ γ) (Fι.tyᴿ γ a)
    -- --       ≡ ε⁻FI.tyᴿ γ a

    -- -- Fι≡ε⁻ : Fι D.≈ ε⁻ FI 
    -- -- Fι≡ε⁻ = D.mk≈ con≡ ty≡
    -- --   where
    -- --   ε⁻FI : D.Hom FI FGFI
    -- --   ε⁻FI = ε⁻ FI
    -- --   module ε⁻FI = ε⁻ FI
    -- --   module ε⁻FI₀ = D.Hom ε⁻FI
    -- --   con≡₀ : (γ : FI.Con) → ι.θ (γ .fst) ≡ return (G₀FI.con γ)
    -- --   con≡₀ (γ , kγ) = 
    -- --     ι.θ γ
    -- --       ≡⟨ {!!} ⟩
    -- --     return (G₀FI.con (γ , kγ)) ∎
    -- --   con≡ : (γ : FI.Con) → Fι.conᴿ γ ≡ ε⁻FI.conᴿ γ
    -- --   con≡ γ = ΣP≡ _ _ (con≡₀ γ)
    -- --   ty≡ : (γ : FI.Con) (a : FI.Ty γ)
    -- --       → subst FGFI.Ty (con≡ γ) (Fι.tyᴿ γ a)
    -- --       ≡ ε⁻FI.tyᴿ γ a

    -- -- g : D.Hom FI FGA
    -- -- g = ε⁻ A D.∘ f
    -- -- module f = D.Hom f
    -- -- module g = D.Hom g

    -- -- η : W.Hom I GA
    -- -- η = G₁ (ε A) W.∘ G₁ g W.∘ ι
    -- -- module η = W.Hom η
    -- -- open η using (θ)

    -- -- Fη : D.Hom (F₀ I) (F₀ (G₀ A))
    -- -- Fη = F₁ η
    -- -- module Fη = F₁ η



    -- -- -- con↓ : ∀ γ
    -- -- --   → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- --   → θ γ ↓
    -- -- -- con↓ γ kγ = G₀A.con↓ (θ γ) (θkγ kγ)

    -- -- -- getCon : ∀ γ
    -- -- --   → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- --   → G₀A.Atom
    -- -- -- getCon γ kγ = G₀A.getConAtom (θ γ) (θkγ kγ)

    -- -- -- ty↓ : ∀ γ a
    -- -- --   → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- --   → (ka : I.[ a ] ≡ I.t̂ γ)
    -- -- --   → θ a ↓
    -- -- -- ty↓ γ a kγ ka =
    -- -- --   G₀A.ty↓ (θ γ) (θ a) (θkγ kγ) (θka kγ ka )

    -- -- -- η : D.Hom (F₀ I) A
    -- -- -- η .D.conᴿ (γ , kγ) =
    -- -- --   {!!}
    -- -- --   where
    -- -- --   cd₁ = con↓ γ
    -- -- -- η .D.tyᴿ (γ , kγ) (a , ka) =
    -- -- --   {!!} 
    -- -- -- η .D.∙ᴿ = {!!}
    -- -- -- η .D.▷ᴿ = {!!}
    -- -- -- η .D.uᴿ = {!!}
    -- -- -- η .D.πᴿ = {!!}
    -- -- -- η .D.σᴿ = {!!}

    -- -- -- η↑ : D.Hom (F₀ I) A↑
    -- -- -- η↑ = D.Lift⇒ ℓA' A D.∘ η

    -- -- -- τ : W.Hom {ℓA = lsuc (lsuc ℓA)} (G₀ (F₀ I)) (G₀ A↑)
    -- -- -- τ = G₁ {!!}

    -- -- -- -- beta : F₁ r D.≈ f
    -- -- -- -- beta =
    -- -- -- --   D.mk≈ {!con≡!} {!ty≡!}
    -- -- -- --   where

    -- -- -- --   conEq : (γ : I.CT) → I.[ γ ] ≡ I.ĉ → G₀A.[ θ γ ] ≡ G₀A.cʰ
    -- -- -- --   conEq γ kγ =
    -- -- -- --     G₀A.[ θ γ ]
    -- -- -- --       ≡⟨ sym (r.[ γ ]) ⟩
    -- -- -- --     θ I.[ γ ]
    -- -- -- --       ≡⟨ cong θ kγ ⟩
    -- -- -- --     θ I.ĉ
    -- -- -- --       ≡⟨ r.ĉ ⟩
    -- -- -- --     G₀A.cʰ ∎
    -- -- -- --     where open ≡-Reasoning

    -- -- -- --   conDef : (γ : I.CT) → I.[ γ ] ≡ I.ĉ → θ γ ↓
    -- -- -- --   conDef γ kγ = (≡→≈ (conEq γ kγ) .∧e₁ .∧e₂ tt*) .∧e₂

    -- -- -- --   tyEq : (γ a : I.CT)
    -- -- -- --     → I.[ γ ] ≡ I.ĉ
    -- -- -- --     → I.[ a ] ≡ I.t̂ γ
    -- -- -- --     → G₀A.[ θ a ] ≡ G₀A.tʰ (θ γ)
    -- -- -- --   tyEq γ a kγ ka =
    -- -- -- --     G₀A.[ θ a ]
    -- -- -- --       ≡⟨ sym (r.[ a ]) ⟩
    -- -- -- --     θ I.[ a ]
    -- -- -- --       ≡⟨ cong θ ka ⟩
    -- -- -- --     θ (I.t̂ γ)
    -- -- -- --       ≡⟨ r.t̂ γ ⟩
    -- -- -- --     G₀A.tʰ (θ γ) ∎
    -- -- -- --     where open ≡-Reasoning

    -- -- -- --   tyDef : (γ a : I.CT)
    -- -- -- --     → I.[ γ ] ≡ I.ĉ
    -- -- -- --     → I.[ a ] ≡ I.t̂ γ
    -- -- -- --     → θ a ↓
    -- -- -- --   tyDef γ a kγ ka =
    -- -- -- --     (≡→≈ (tyEq γ a kγ ka) .∧e₁ .∧e₂ (∧i tt* , conDef γ kγ)) .∧e₂

    -- -- -- --   conRet : (γ : I.CT)
    -- -- -- --     → I.[ γ ] ≡ I.ĉ
    -- -- -- --     → ΣP A.Con λ γ₀ → θ γ ≡ return (G₀A.con γ₀)
    -- -- -- --   conRet γ kγ = G₀A.[]≡cʰ→return (conEq γ kγ)

    -- -- -- --   tyRet : (γ a : I.CT)
    -- -- -- --     → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- -- --     → (ka : I.[ a ] ≡ I.t̂ γ)
    -- -- -- --     → Σ A.Con λ γ₀
    -- -- -- --     → ΣP (A.Ty γ₀) λ a₀
    -- -- -- --     → θ a ≡ return (G₀A.ty γ₀ a₀)
    -- -- -- --     ∧ θ γ ≡ return (G₀A.con γ₀)
    -- -- -- --   tyRet γ a kγ ka = G₀A.[]≡tʰ→return (tyEq γ a kγ ka) (tyDef γ a kγ ka)

    -- -- -- --   ▷-inv : (γ a : I.CT)
    -- -- -- --     → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- -- --     → (ka : I.[ a ] ≡ I.t̂ γ)
    -- -- -- --     → (▷↓ : θ (I.▷ γ a) ↓)
    -- -- -- --     → θ γ ↓
    -- -- -- --     ∧ θ a ↓
    -- -- -- --   ▷-inv γ a kγ ka ▷↓ = ∧i γ↓ , a↓
    -- -- -- --     where
    -- -- -- --     ▷↓' : G₀A.▷ (θ γ) (θ a) ↓
    -- -- -- --     ▷↓' = substp (_↓) (r.▷ γ a kγ ka) ▷↓
    -- -- -- --     γ↓ : θ γ ↓
    -- -- -- --     γ↓ = G₀A.▷⁻-γ (θ γ) (θ a) ▷↓'
    -- -- -- --     a↓ : θ a ↓
    -- -- -- --     a↓ = G₀A.▷⁻-a (θ γ) (θ a) ▷↓'

    -- -- -- --   record P (x : I.CT) : Prop (lsuc ℓA) where
    -- -- -- --     field
    -- -- -- --       Conβ :
    -- -- -- --         (kx : I.[ x ] ≡ I.ĉ)
    -- -- -- --         → θ x ≡ f.conᴿ (x , kx) .fst
    -- -- -- --       Tyβ : 
    -- -- -- --         (γ : I.CT)
    -- -- -- --         → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- -- --         → (kx : I.[ x ] ≡ I.t̂ γ)
    -- -- -- --         → θ x ≡ f.tyᴿ (γ , kγ) (x , kx) .fst
    -- -- -- --       ▷-con-γ : ∀ γ a
    -- -- -- --         → x ≡ I.▷ γ a
    -- -- -- --         → I.[ I.▷ γ a ] ≡ I.ĉ
    -- -- -- --         → I.[ γ ] ≡ I.ĉ
    -- -- -- --       ▷-con-a : ∀ γ a
    -- -- -- --         → x ≡ I.▷ γ a
    -- -- -- --         → I.[ I.▷ γ a ] ≡ I.ĉ
    -- -- -- --         → I.[ a ] ≡ I.t̂ γ
    -- -- -- --       ▷-ty-absurd : ∀ γ a δ
    -- -- -- --         → x ≡ I.▷ γ a
    -- -- -- --         → (kγ : I.[ γ ] ≡ I.ĉ)
    -- -- -- --         → (ka : I.[ a ] ≡ I.t̂ δ)
    -- -- -- --         → I.[ I.▷ γ a ] ≡ I.t̂ δ
    -- -- -- --         → ⊥
    -- -- -- --       u-con-absurd : ∀ {γ}
    -- -- -- --         → I.[ I.u γ ] ≡ I.ĉ
    -- -- -- --         → ⊥
    -- -- -- --       u-ty-inv : ∀ {γ γ'}
    -- -- -- --         → I.[ I.u γ ] ≡ I.t̂ γ'
    -- -- -- --         → I.[ γ ] ≡ I.ĉ ∧ᵖ λ _ → γ' ≡ γ

    -- -- -- --   Pᵂ : W.Algebra (lsuc ℓA)
    -- -- -- --   Pᵂ = record
    -- -- -- --     { CT = CT
    -- -- -- --     ; [_] = [_]
    -- -- -- --     -- ; k̂ = k̂
    -- -- -- --     -- ; kk̂ = kk̂
    -- -- -- --     -- ; ĉ = ĉ
    -- -- -- --     -- ; kĉ = kĉ
    -- -- -- --     -- ; t̂ = t̂
    -- -- -- --     -- ; kt̂ = kt̂
    -- -- -- --     -- ; ∙ = ∙
    -- -- -- --     -- ; k∙ = k∙
    -- -- -- --     -- ; ▷ = ▷
    -- -- -- --     -- ; k▷ = k▷
    -- -- -- --     -- ; u = u
    -- -- -- --     -- ; ku = ku
    -- -- -- --     -- ; π = π
    -- -- -- --     -- ; kπ = kπ
    -- -- -- --     -- ; σ = σ
    -- -- -- --     -- ; kσ = kσ
    -- -- -- --     -- ; σ▷ = σ▷
    -- -- -- --     -- ; σπ = σπ
    -- -- -- --     }
    -- -- -- --     where
    -- -- -- --     CT : Set (lsuc ℓA)
    -- -- -- --     CT = ΣP I.CT P

    -- -- -- --     open P

    -- -- -- --     [_] : CT → CT
    -- -- -- --     [ x , px ] = I.[ x ] , p
    -- -- -- --       where
    -- -- -- --       p : P I.[ x ]
    -- -- -- --       p .Conβ kx = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} q)
    -- -- -- --         where
    -- -- -- --         q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
    -- -- -- --         q = trans (cong G₀A.[_] (sym r.[ x ])) (conEq (I.[ x ]) kx)
    -- -- -- --       p .Tyβ γ kγ kx = ⊥e (G₀A.[[x]]≢tʰ {θ x} {θ γ} x↓ q)
    -- -- -- --         where
    -- -- -- --         γ↓ : θ γ ↓
    -- -- -- --         γ↓ = conDef γ kγ

    -- -- -- --         q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.tʰ (θ γ)
    -- -- -- --         q = trans (cong G₀A.[_] (sym r.[ x ])) (tyEq γ (I.[ x ]) kγ kx)

    -- -- -- --         q≈ : G₀A.[ G₀A.[ θ x ] ] ≈ G₀A.tʰ (θ γ)
    -- -- -- --         q≈ = ≡→≈ q

    -- -- -- --         x↓ : θ x ↓
    -- -- -- --         x↓ = (q≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂
    -- -- -- --       p .▷-con-γ γ a [x]≡▷ k▷ = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} q)
    -- -- -- --         where
    -- -- -- --         kx : I.[ I.[ x ] ] ≡ I.ĉ
    -- -- -- --         kx = trans (cong I.[_] [x]≡▷) k▷
    -- -- -- --         q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
    -- -- -- --         q = trans (cong G₀A.[_] (sym r.[ x ]))
    -- -- -- --                     (conEq (I.[ x ]) kx)
    -- -- -- --       p .▷-con-a γ a [x]≡▷ k▷ = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} q)
    -- -- -- --         where
    -- -- -- --         kx : I.[ I.[ x ] ] ≡ I.ĉ
    -- -- -- --         kx = trans (cong I.[_] [x]≡▷) k▷
    -- -- -- --         q : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
    -- -- -- --         q = trans (cong G₀A.[_] (sym r.[ x ]))
    -- -- -- --                     (conEq (I.[ x ]) kx)
    -- -- -- --       p .▷-ty-absurd = {!!}
    -- -- -- --       p .u-con-absurd = P.u-con-absurd px
    -- -- -- --       p .u-ty-inv = P.u-ty-inv px

    -- -- -- --     k̂ : CT
    -- -- -- --     k̂ = I.k̂ , p
    -- -- -- --       where
    -- -- -- --       p : P I.k̂
    -- -- -- --       p .Conβ kk̂ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
    -- -- -- --         where
    -- -- -- --         k̂≡ĉ : GA.k̂ ≡ GA.ĉ
    -- -- -- --         k̂≡ĉ =
    -- -- -- --           trans
    -- -- -- --             (sym GA.kk̂)
    -- -- -- --             (trans (cong GA.[_] (sym r.k̂))
    -- -- -- --                       (conEq I.k̂ kk̂))
    -- -- -- --       p .Tyβ γ kγ ka = ⊥e (G₀A.[kʰ]≢tʰ {x* = θ γ} q)
    -- -- -- --         where
    -- -- -- --         q : GA.[ GA.k̂ ] ≡ GA.t̂ (θ γ)
    -- -- -- --         q = trans (cong GA.[_] (sym r.k̂))
    -- -- -- --                       (tyEq γ I.k̂ kγ ka)
    -- -- -- --       p .▷-con-γ γ a x≡▷ k▷ = ⊥e (G₀A.[kʰ]≢cʰ {!!})
    -- -- -- --         where
    -- -- -- --         q : GA.[ GA.k̂ ] ≡ GA.ĉ
    -- -- -- --         q = trans (cong GA.[_] (sym r.k̂))
    -- -- -- --                       (conEq I.k̂ {!!})
    -- -- -- --       p .▷-con-a γ a x x₁ = {!!}
    -- -- -- --       p .▷-ty-absurd = {!!}
    -- -- -- --       p .u-con-absurd = {!!}
    -- -- -- --       p .u-ty-inv = {!!}

    -- -- -- --     kk̂ : [ k̂ ] ≡ k̂
    -- -- -- --     kk̂ = ΣP≡ _ _ I.kk̂

    -- -- -- --     ĉ : CT
    -- -- -- --     ĉ = I.ĉ , p
    -- -- -- --       where
    -- -- -- --       p : P I.ĉ
    -- -- -- --       p .Conβ kĉ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
    -- -- -- --         where
    -- -- -- --         k̂≡ĉ : GA.k̂ ≡ GA.ĉ
    -- -- -- --         k̂≡ĉ =
    -- -- -- --           trans
    -- -- -- --             (sym GA.kĉ)
    -- -- -- --             (trans (cong GA.[_] (sym r.ĉ))
    -- -- -- --                       (conEq I.ĉ kĉ))
    -- -- -- --       p .Tyβ γ kγ ka = ⊥e (G₀A.[cʰ]≢tʰ {x* = θ γ} q)
    -- -- -- --         where
    -- -- -- --         q : GA.[ GA.ĉ ] ≡ GA.t̂ (θ γ)
    -- -- -- --         q = trans (cong GA.[_] (sym r.ĉ))
    -- -- -- --                       (tyEq γ I.ĉ kγ ka)
    -- -- -- --       p .▷-con-γ = {!!}
    -- -- -- --       p .▷-con-a = {!!}
    -- -- -- --       p .▷-ty-absurd = {!!}
    -- -- -- --       p .u-con-absurd = {!!}
    -- -- -- --       p .u-ty-inv = {!!}

    -- -- -- --     kĉ : [ ĉ ] ≡ k̂
    -- -- -- --     kĉ = ΣP≡ _ _ I.kĉ

    -- -- -- -- --     t̂ : CT → CT
    -- -- -- -- --     t̂ (x , ∧i cx , tx) = I.t̂ x , ∧i ct , tyt
    -- -- -- -- --       where
    -- -- -- -- --       open ≡-Reasoning
    -- -- -- -- --       ct : Conβ (I.t̂ x)
    -- -- -- -- --       ct kx = ⊥e (G₀A.[tʰ]≢cʰ {x* = θ x} p)
    -- -- -- -- --         where
    -- -- -- -- --         p : GA.[ GA.t̂ (θ x) ] ≡ GA.ĉ
    -- -- -- -- --         p =
    -- -- -- -- --           GA.[ GA.t̂ (θ x) ]
    -- -- -- -- --             ≡⟨ cong GA.[_] (sym (r.t̂ x)) ⟩
    -- -- -- -- --           GA.[ θ (I.t̂ x) ]
    -- -- -- -- --             ≡⟨ sym (r.[ I.t̂ x ]) ⟩
    -- -- -- -- --           θ I.[ I.t̂ x ]
    -- -- -- -- --             ≡⟨ cong θ kx ⟩
    -- -- -- -- --           θ I.ĉ
    -- -- -- -- --             ≡⟨ r.ĉ ⟩
    -- -- -- -- --           GA.ĉ ∎
    -- -- -- -- --       tyt : Tyβ (I.t̂ x)
    -- -- -- -- --       tyt γ kγ ka with tyRet γ (I.t̂ x) kγ ka
    -- -- -- -- --       ... | γ₀ , a₀ , qeq = ⊥e* (G₀A.encode (u .snd))
    -- -- -- -- --         where
    -- -- -- -- --         p : G₀A.tʰ (θ x) ≡ return (G₀A.ty γ₀ a₀)
    -- -- -- -- --         p = trans (sym (r.t̂ x)) (qeq .∧e₁)
    -- -- -- -- --         u : ΣP G₀A.Atom λ z → G₀A.t̂ z ≡ G₀A.ty γ₀ a₀
    -- -- -- -- --         u = map-return-inj G₀A.t̂ (θ x) (G₀A.ty γ₀ a₀) p

    -- -- -- -- --     kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
    -- -- -- -- --     kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (I.kt̂ x (cong fst kγ))

    -- -- -- -- --     ∙ : CT
    -- -- -- -- --     ∙ = I.∙ , ∧i c∙ , t∙
    -- -- -- -- --       where
    -- -- -- -- --       c∙ : Conβ I.∙
    -- -- -- -- --       c∙ k∙ =
    -- -- -- -- --         θ I.∙
    -- -- -- -- --           ≡⟨ r.∙ ⟩
    -- -- -- -- --         GA.∙
    -- -- -- -- --           ≡⟨ sym (cong fst f.∙ᴿ) ⟩
    -- -- -- -- --         f.conᴿ (I.∙ , k∙) .fst ∎
    -- -- -- -- --         where open ≡-Reasoning
    -- -- -- -- --       t∙ : Tyβ I.∙
    -- -- -- -- --       t∙ γ kγ ka = ⊥e (G₀A.cʰ≢tʰ {x = θ γ} p)
    -- -- -- -- --         where
    -- -- -- -- --         p : GA.ĉ ≡ GA.t̂ (θ γ)
    -- -- -- -- --         p =
    -- -- -- -- --           trans
    -- -- -- -- --             (sym GA.k∙)
    -- -- -- -- --             (trans (cong GA.[_] (sym r.∙))
    -- -- -- -- --                       (tyEq γ I.∙ kγ ka))

    -- -- -- -- --     k∙ : [ ∙ ] ≡ ĉ
    -- -- -- -- --     k∙ = ΣP≡ _ _ I.k∙

    -- -- -- -- --     ▷ : CT → CT → CT
    -- -- -- -- --     ▷ (γ , pγ) (a , pa) =
    -- -- -- -- --       I.▷ γ a , ∧i c▷ , t▷
    -- -- -- -- --       where
    -- -- -- -- --       c▷ : Conβ (I.▷ γ a)
    -- -- -- -- --       c▷ kx =
    -- -- -- -- --         θ (I.▷ γ a)
    -- -- -- -- --           ≡⟨ r.▷ γ a kγ ka ⟩
    -- -- -- -- --         GA.▷ (θ γ) (θ a)
    -- -- -- -- --           ≡⟨ cong₂ GA.▷ (pγ .∧e₁ kγ) (pa .∧e₂ γ kγ ka) ⟩
    -- -- -- -- --         GA.▷
    -- -- -- -- --           (f.conᴿ (γ , kγ) .fst)
    -- -- -- -- --           (f.tyᴿ (γ , kγ) (a , ka) .fst)
    -- -- -- -- --           ≡⟨ sym (cong fst (f.▷ᴿ (γ , kγ) (a , ka))) ⟩
    -- -- -- -- --         f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
    -- -- -- -- --           ≡⟨ p▷ ⟩
    -- -- -- -- --         f.conᴿ (I.▷ γ a , kx) .fst ∎
    -- -- -- -- --         where
    -- -- -- -- --         open ≡-Reasoning
    -- -- -- -- --         kγa : I.[ γ ] ≡ I.ĉ ∧ᵖ λ kγ
    -- -- -- -- --           → I.[ a ] ≡ I.t̂ γ
    -- -- -- -- --         kγa = {!▷-con-inv kx!}
    -- -- -- -- --         kγ = kγa .∧e₁
    -- -- -- -- --         ka = kγa .∧e₂
    -- -- -- -- --         p▷ : f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
    -- -- -- -- --            ≡ f.conᴿ (I.▷ γ a , kx) .fst
    -- -- -- -- --         p▷ = cong fst (cong f.conᴿ (ΣP≡ _ _ refl))
    -- -- -- -- --       t▷ : Tyβ (I.▷ γ a)
    -- -- -- -- --       t▷ γ kγ ka = ⊥e {!∀ δ → {!▷-ty-absurd γ kγ a {!ka!} δ!}!}

    -- -- -- -- --     k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
    -- -- -- -- --     k▷ (γ , pγ) (a , pa) kγ ka = ΣP≡ _ _ (I.k▷ γ a (cong fst kγ) (cong fst ka))

    -- -- -- -- --     u : CT → CT
    -- -- -- -- --     u (γ , pγ) =
    -- -- -- -- --       I.u γ , ∧i cu , tu
    -- -- -- -- --       where
    -- -- -- -- --       cu : Conβ (I.u γ)
    -- -- -- -- --       cu = {!!} 
    -- -- -- -- --       tu : Tyβ (I.u γ)
    -- -- -- -- --       tu γ kγ ka = {!!}

    -- -- -- -- --     ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
    -- -- -- -- --     ku = {!!}

    -- -- -- -- --     π : CT → CT → CT → CT
    -- -- -- -- --     π = {!!}

    -- -- -- -- --     kπ : (γ a b : CT)
    -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- --       → [ π γ a b ] ≡ t̂ γ
    -- -- -- -- --     kπ = {!!}

    -- -- -- -- --     σ : CT → CT → CT → CT
    -- -- -- -- --     σ = {!!}

    -- -- -- -- --     kσ : (γ a b : CT)
    -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- --       → [ σ γ a b ] ≡ t̂ γ
    -- -- -- -- --     kσ = {!!}

    -- -- -- -- --     σ▷ : (γ a b : CT)
    -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- --       → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
    -- -- -- -- --     σ▷ = {!!}

    -- -- -- -- --     σπ : (γ a b d : CT)
    -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- --       → [ d ] ≡ t̂ (▷ (▷ γ a) b)
    -- -- -- -- --       → π γ a (π (▷ γ a) b d) ≡ π γ (σ γ a b) d
    -- -- -- -- --     σπ = {!!}

    -- -- -- -- --   allP : (x : I.CT) → P x
    -- -- -- -- --   allP x = {!!}

    -- -- -- -- --   con≡ : (γ : D.Con (F₀ I)) → F₁.conᴿ (invFG f) γ ≡ f.conᴿ γ
    -- -- -- -- --   con≡ (γ , kγ) =
    -- -- -- -- --     ΣP≡ _ _ (allP γ .∧e₁ kγ)

    -- -- -- -- --   ty≡ : (γ : D.Con (F₀ I)) (a : F₀ I .D.Ty γ) →
    -- -- -- -- --          subst (D.Ty (F₀ (G₀ A))) (con≡ γ) (D.tyᴿ (F₁ (invFG f)) γ a) ≡
    -- -- -- -- --          f.tyᴿ γ a
    -- -- -- -- --   ty≡ (γ , kγ) (a , ka) = {!!}

    -- -- -- -- -- --     [_] : CT → CT
    -- -- -- -- -- --     [ x , ∧i cx , cy ] = I.[ x ] , ∧i c[x] , t[x]
    -- -- -- -- -- --       where
    -- -- -- -- -- --       c[x] : Conβ I.[ x ]
    -- -- -- -- -- --       c[x] kx = ⊥e (G₀A.[[x]]≢cʰ {x* = θ x} p)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         p : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.cʰ
    -- -- -- -- -- --         p = trans (cong G₀A.[_] (sym r.[ x ])) (conEq (I.[ x ]) kx)
    -- -- -- -- -- --       t[x] : Tyβ I.[ x ]
    -- -- -- -- -- --       t[x] γ kγ ka =
    -- -- -- -- -- --         ⊥e (G₀A.[[x]]≢tʰ
    -- -- -- -- -- --           {x* = θ x}
    -- -- -- -- -- --           {y* = θ γ}
    -- -- -- -- -- --           x↓
    -- -- -- -- -- --           p)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         γ↓ : θ γ ↓
    -- -- -- -- -- --         γ↓ = conDef γ kγ

    -- -- -- -- -- --         p : G₀A.[ G₀A.[ θ x ] ] ≡ G₀A.tʰ (θ γ)
    -- -- -- -- -- --         p = trans (cong G₀A.[_] (sym r.[ x ])) (tyEq γ (I.[ x ]) kγ ka)

    -- -- -- -- -- --         p≈ : G₀A.[ G₀A.[ θ x ] ] ≈ G₀A.tʰ (θ γ)
    -- -- -- -- -- --         p≈ = ≡→≈ p

    -- -- -- -- -- --         x↓ : θ x ↓
    -- -- -- -- -- --         x↓ = (p≈ .∧e₁ .∧e₂ (∧i tt* , γ↓)) .∧e₂ .∧e₂

    -- -- -- -- -- --     k̂ : CT
    -- -- -- -- -- --     k̂ = I.k̂ , ∧i ck̂ , tk̂
    -- -- -- -- -- --       where
    -- -- -- -- -- --       ck̂ : Conβ Fr.A.k̂
    -- -- -- -- -- --       ck̂ kk̂ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         k̂≡ĉ : GA.k̂ ≡ GA.ĉ
    -- -- -- -- -- --         k̂≡ĉ =
    -- -- -- -- -- --           trans
    -- -- -- -- -- --             (sym GA.kk̂)
    -- -- -- -- -- --             (trans (cong GA.[_] (sym r.k̂))
    -- -- -- -- -- --                       (conEq I.k̂ kk̂))
    -- -- -- -- -- --       tk̂ : Tyβ Fr.A.k̂
    -- -- -- -- -- --       tk̂ γ kγ ka = ⊥e (G₀A.[kʰ]≢tʰ {x* = θ γ} p)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         p : GA.[ GA.k̂ ] ≡ GA.t̂ (θ γ)
    -- -- -- -- -- --         p = trans (cong GA.[_] (sym r.k̂)) (tyEq γ I.k̂ kγ ka)

    -- -- -- -- -- --     kk̂ : [ k̂ ] ≡ k̂
    -- -- -- -- -- --     kk̂ = ΣP≡ _ _ I.kk̂

    -- -- -- -- -- --     ĉ : CT
    -- -- -- -- -- --     ĉ = I.ĉ , ∧i cĉ , tĉ
    -- -- -- -- -- --       where
    -- -- -- -- -- --       cĉ : Conβ I.ĉ
    -- -- -- -- -- --       cĉ kĉ = ⊥e (G₀A.kʰ≢cʰ k̂≡ĉ)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         k̂≡ĉ : GA.k̂ ≡ GA.ĉ
    -- -- -- -- -- --         k̂≡ĉ =
    -- -- -- -- -- --           trans
    -- -- -- -- -- --             (sym GA.kĉ)
    -- -- -- -- -- --             (trans (cong GA.[_] (sym r.ĉ))
    -- -- -- -- -- --                       (conEq I.ĉ kĉ))
    -- -- -- -- -- --       tĉ : Tyβ I.ĉ
    -- -- -- -- -- --       tĉ γ kγ ka = ⊥e (G₀A.[cʰ]≢tʰ {x* = θ γ} p)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         p : GA.[ GA.ĉ ] ≡ GA.t̂ (θ γ)
    -- -- -- -- -- --         p = trans (cong GA.[_] (sym r.ĉ)) (tyEq γ I.ĉ kγ ka)

    -- -- -- -- -- --     kĉ : [ ĉ ] ≡ k̂
    -- -- -- -- -- --     kĉ = ΣP≡ _ _ I.kĉ

    -- -- -- -- -- --     t̂ : CT → CT
    -- -- -- -- -- --     t̂ (x , ∧i cx , tx) = I.t̂ x , ∧i ct , tyt
    -- -- -- -- -- --       where
    -- -- -- -- -- --       open ≡-Reasoning
    -- -- -- -- -- --       ct : Conβ (I.t̂ x)
    -- -- -- -- -- --       ct kx = ⊥e (G₀A.[tʰ]≢cʰ {x* = θ x} p)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         p : GA.[ GA.t̂ (θ x) ] ≡ GA.ĉ
    -- -- -- -- -- --         p =
    -- -- -- -- -- --           GA.[ GA.t̂ (θ x) ]
    -- -- -- -- -- --             ≡⟨ cong GA.[_] (sym (r.t̂ x)) ⟩
    -- -- -- -- -- --           GA.[ θ (I.t̂ x) ]
    -- -- -- -- -- --             ≡⟨ sym (r.[ I.t̂ x ]) ⟩
    -- -- -- -- -- --           θ I.[ I.t̂ x ]
    -- -- -- -- -- --             ≡⟨ cong θ kx ⟩
    -- -- -- -- -- --           θ I.ĉ
    -- -- -- -- -- --             ≡⟨ r.ĉ ⟩
    -- -- -- -- -- --           GA.ĉ ∎
    -- -- -- -- -- --       tyt : Tyβ (I.t̂ x)
    -- -- -- -- -- --       tyt γ kγ ka with tyRet γ (I.t̂ x) kγ ka
    -- -- -- -- -- --       ... | γ₀ , a₀ , qeq = ⊥e* (G₀A.encode (u .snd))
    -- -- -- -- -- --         where
    -- -- -- -- -- --         p : G₀A.tʰ (θ x) ≡ return (G₀A.ty γ₀ a₀)
    -- -- -- -- -- --         p = trans (sym (r.t̂ x)) (qeq .∧e₁)
    -- -- -- -- -- --         u : ΣP G₀A.Atom λ z → G₀A.t̂ z ≡ G₀A.ty γ₀ a₀
    -- -- -- -- -- --         u = map-return-inj G₀A.t̂ (θ x) (G₀A.ty γ₀ a₀) p

    -- -- -- -- -- --     kt̂ : (γ : CT) → [ γ ] ≡ ĉ → [ t̂ γ ] ≡ k̂
    -- -- -- -- -- --     kt̂ (x , ∧i cx , tx) kγ = ΣP≡ _ _ (I.kt̂ x (cong fst kγ))

    -- -- -- -- -- --     ∙ : CT
    -- -- -- -- -- --     ∙ = I.∙ , ∧i c∙ , t∙
    -- -- -- -- -- --       where
    -- -- -- -- -- --       c∙ : Conβ I.∙
    -- -- -- -- -- --       c∙ k∙ =
    -- -- -- -- -- --         θ I.∙
    -- -- -- -- -- --           ≡⟨ r.∙ ⟩
    -- -- -- -- -- --         GA.∙
    -- -- -- -- -- --           ≡⟨ sym (cong fst f.∙ᴿ) ⟩
    -- -- -- -- -- --         f.conᴿ (I.∙ , k∙) .fst ∎
    -- -- -- -- -- --         where open ≡-Reasoning
    -- -- -- -- -- --       t∙ : Tyβ I.∙
    -- -- -- -- -- --       t∙ γ kγ ka = ⊥e (G₀A.cʰ≢tʰ {x = θ γ} p)
    -- -- -- -- -- --         where
    -- -- -- -- -- --         p : GA.ĉ ≡ GA.t̂ (θ γ)
    -- -- -- -- -- --         p =
    -- -- -- -- -- --           trans
    -- -- -- -- -- --             (sym GA.k∙)
    -- -- -- -- -- --             (trans (cong GA.[_] (sym r.∙))
    -- -- -- -- -- --                       (tyEq γ I.∙ kγ ka))

    -- -- -- -- -- --     k∙ : [ ∙ ] ≡ ĉ
    -- -- -- -- -- --     k∙ = ΣP≡ _ _ I.k∙

    -- -- -- -- -- --     ▷ : CT → CT → CT
    -- -- -- -- -- --     ▷ (γ , pγ) (a , pa) =
    -- -- -- -- -- --       I.▷ γ a , ∧i c▷ , t▷
    -- -- -- -- -- --       where
    -- -- -- -- -- --       c▷ : Conβ (I.▷ γ a)
    -- -- -- -- -- --       c▷ kx =
    -- -- -- -- -- --         θ (I.▷ γ a)
    -- -- -- -- -- --           ≡⟨ r.▷ γ a kγ ka ⟩
    -- -- -- -- -- --         GA.▷ (θ γ) (θ a)
    -- -- -- -- -- --           ≡⟨ cong₂ GA.▷ (pγ .∧e₁ kγ) (pa .∧e₂ γ kγ ka) ⟩
    -- -- -- -- -- --         GA.▷
    -- -- -- -- -- --           (f.conᴿ (γ , kγ) .fst)
    -- -- -- -- -- --           (f.tyᴿ (γ , kγ) (a , ka) .fst)
    -- -- -- -- -- --           ≡⟨ sym (cong fst (f.▷ᴿ (γ , kγ) (a , ka))) ⟩
    -- -- -- -- -- --         f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
    -- -- -- -- -- --           ≡⟨ p▷ ⟩
    -- -- -- -- -- --         f.conᴿ (I.▷ γ a , kx) .fst ∎
    -- -- -- -- -- --         where
    -- -- -- -- -- --         open ≡-Reasoning
    -- -- -- -- -- --         kγa : I.[ γ ] ≡ I.ĉ ∧ᵖ λ kγ
    -- -- -- -- -- --           → I.[ a ] ≡ I.t̂ γ
    -- -- -- -- -- --         kγa = ▷-con-inv kx
    -- -- -- -- -- --         kγ = kγa .∧e₁
    -- -- -- -- -- --         ka = kγa .∧e₂
    -- -- -- -- -- --         p▷ : f.conᴿ (I.▷ γ a , I.k▷ γ a kγ ka) .fst
    -- -- -- -- -- --            ≡ f.conᴿ (I.▷ γ a , kx) .fst
    -- -- -- -- -- --         p▷ = cong fst (cong f.conᴿ (ΣP≡ _ _ refl))
    -- -- -- -- -- --       t▷ : Tyβ (I.▷ γ a)
    -- -- -- -- -- --       t▷ γ kγ ka = ⊥e {!∀ δ → {!▷-ty-absurd γ kγ a {!ka!} δ!}!}

    -- -- -- -- -- --     k▷ : (γ a : CT) → [ γ ] ≡ ĉ → [ a ] ≡ t̂ γ → [ ▷ γ a ] ≡ ĉ
    -- -- -- -- -- --     k▷ (γ , pγ) (a , pa) kγ ka = ΣP≡ _ _ (I.k▷ γ a (cong fst kγ) (cong fst ka))

    -- -- -- -- -- --     u : CT → CT
    -- -- -- -- -- --     u (γ , pγ) =
    -- -- -- -- -- --       I.u γ , ∧i cu , tu
    -- -- -- -- -- --       where
    -- -- -- -- -- --       cu : Conβ (I.u γ)
    -- -- -- -- -- --       cu = {!!} 
    -- -- -- -- -- --       tu : Tyβ (I.u γ)
    -- -- -- -- -- --       tu γ kγ ka = {!!}

    -- -- -- -- -- --     ku : (γ : CT) → [ γ ] ≡ ĉ → [ u γ ] ≡ t̂ γ
    -- -- -- -- -- --     ku = {!!}

    -- -- -- -- -- --     π : CT → CT → CT → CT
    -- -- -- -- -- --     π = {!!}

    -- -- -- -- -- --     kπ : (γ a b : CT)
    -- -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- -- --       → [ π γ a b ] ≡ t̂ γ
    -- -- -- -- -- --     kπ = {!!}

    -- -- -- -- -- --     σ : CT → CT → CT → CT
    -- -- -- -- -- --     σ = {!!}

    -- -- -- -- -- --     kσ : (γ a b : CT)
    -- -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- -- --       → [ σ γ a b ] ≡ t̂ γ
    -- -- -- -- -- --     kσ = {!!}

    -- -- -- -- -- --     σ▷ : (γ a b : CT)
    -- -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- -- --       → ▷ (▷ γ a) b ≡ ▷ γ (σ γ a b)
    -- -- -- -- -- --     σ▷ = {!!}

    -- -- -- -- -- --     σπ : (γ a b d : CT)
    -- -- -- -- -- --       → [ γ ] ≡ ĉ
    -- -- -- -- -- --       → [ a ] ≡ t̂ γ
    -- -- -- -- -- --       → [ b ] ≡ t̂ (▷ γ a)
    -- -- -- -- -- --       → [ d ] ≡ t̂ (▷ (▷ γ a) b)
    -- -- -- -- -- --       → π γ a (π (▷ γ a) b d) ≡ π γ (σ γ a b) d
    -- -- -- -- -- --     σπ = {!!}

    -- -- -- -- -- --   allP : (x : I.CT) → P x
    -- -- -- -- -- --   allP x = {!!}

    -- -- -- -- -- --   con≡ : (γ : D.Con (F₀ I)) → F₁.conᴿ (invFG f) γ ≡ f.conᴿ γ
    -- -- -- -- -- --   con≡ (γ , kγ) =
    -- -- -- -- -- --     ΣP≡ _ _ (allP γ .∧e₁ kγ)

    -- -- -- -- -- --   ty≡ : (γ : D.Con (F₀ I)) (a : F₀ I .D.Ty γ) →
    -- -- -- -- -- --          subst (D.Ty (F₀ (G₀ A))) (con≡ γ) (D.tyᴿ (F₁ (invFG f)) γ a) ≡
    -- -- -- -- -- --          f.tyᴿ γ a
    -- -- -- -- -- --   ty≡ (γ , kγ) (a , ka) = {!!}

    -- -- -- -- -- -- recUniqueᴰ : {A : D.Algebra ℓA} → (f : D.Hom FI A) → f D.≈ recᴰ A
    -- -- -- -- -- -- recUniqueᴰ {A = A} f = D≈.trans FI A (D≈.sym (F₀ I) A β) η
    -- -- -- -- -- --   where
    -- -- -- -- -- --   module D≈ {ℓA} {ℓB} A B = ≈.Setoid (D.HomSetoid {ℓA} {ℓB} A B)
    -- -- -- -- -- --   module Dᶜ ℓA = Category (D.Cat ℓA)
    -- -- -- -- -- --   module F ℓA = Functor (F ℓA)
    -- -- -- -- -- --   q : D.Hom FI (F₀ (G₀ A))
    -- -- -- -- -- --   q = ε⁻ A D.∘ f
    -- -- -- -- -- --   β : (ε A D.∘ F₁ (invFG q)) D.≈ f
    -- -- -- -- -- --   β =
    -- -- -- -- -- --     ε A D.∘ F₁ (invFG q)
    -- -- -- -- -- --       ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ A)) A {ε A}) (invFG-beta q) ⟩
    -- -- -- -- -- --     ε A D.∘ (ε⁻ A D.∘ f)
    -- -- -- -- -- --       ≈⟨ D≈.refl FI A ⟩
    -- -- -- -- -- --     f ∎
    -- -- -- -- -- --     where
    -- -- -- -- -- --     open ≈.≈syntax {S = D.HomSetoid FI A}
    -- -- -- -- -- --   η : (ε A D.∘ F₁ (invFG q)) D.≈ recᴰ A
    -- -- -- -- -- --   η =
    -- -- -- -- -- --     ε A D.∘ F₁ (invFG q)
    -- -- -- -- -- --       ≈⟨ D.∘-resp-≈ (D≈.refl (F₀ (G₀ A)) A {ε A})
    -- -- -- -- -- --                     (F.resp (lsuc ℓA) (recUniqueᵂ (invFG q))) ⟩
    -- -- -- -- -- --     ε A D.∘ F₁ (recᵂ (G₀ A)) ∎
    -- -- -- -- -- --     where
    -- -- -- -- -- --     open ≈.≈syntax {S = D.HomSetoid FI A}
