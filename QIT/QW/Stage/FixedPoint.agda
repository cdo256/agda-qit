{-# OPTIONS --type-in-type #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Plump.Algebra
open import QIT.Relation.Binary using (wf-rec)
open import QIT.QW.Signature
open import QIT.Relation.SetQuotient

-- Fiore--Pitts--Steenkamp's stages obtained by iterating the free term monad.
module QIT.QW.Stage.FixedPoint
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (Zᴬ : PlumpAlgebra (sig .Sig.S) (sig .Sig.P))
  where

open FunExt funExt*

open Sig sig
module Z = PlumpAlgebra Zᴬ
open import QIT.Plump.Properties Zᴬ
open import QIT.Plump.Size
open import QIT.QW.Equation S P ℓV

Size = Z.Z

sizeStr : SizeStr Size
sizeStr = plumpSizeStr Zᴬ

open SizedTypes sizeStr public

Dᵇ-type : (i : Size) → Set _
Dᵇ-type i = Πᵇ i λ _ → Set ℓV

τᵇ-type : (i : Size) → Dᵇ-type i → Set _
τᵇ-type i Dᵇ =
  Πᵇ i λ j {j<i} →
  Πᵇ j λ k {k<j} →
  Expr (Dᵇ k {<ᵇ<ᵇ j<i k<j}) → Dᵇ j {j<i}

record IdxStruct : Set _ where
  constructor mkIdxStruct
  field
    D : Size → Set ℓV
    τ : ∀ i → Πᵇ i λ j → Expr (D j) → D i
open IdxStruct public

record IdxStructᵇ (i : Size) : Set _ where
  constructor mkIdxStructᵇ
  field
    Dᵇ : Dᵇ-type i
    τᵇ : τᵇ-type i Dᵇ
open IdxStructᵇ public

IdxStructᵇ-ext : ∀ {i} {A B : IdxStructᵇ i}
  → (p : Dᵇ A ≡ Dᵇ B)
  → subst (λ X → τᵇ-type i X) p (τᵇ A) ≡ τᵇ B
  → A ≡ B
IdxStructᵇ-ext {A = A} ≡.refl q = ≡.cong (mkIdxStructᵇ (Dᵇ A)) q

infixl 6 _↓_ _↓ᵇ_

_↓_ : IdxStruct → ∀ i → IdxStructᵇ i
(A ↓ i) .Dᵇ j = A .D j
(A ↓ i) .τᵇ j k {k<j} t = A .τ j k {k<j} t

_↓ᵇ_ : {i : Size} → IdxStructᵇ i → ∀ j {j<i : j <ᵇ i} → IdxStructᵇ j
((A ↓ᵇ j) {j<i}) .Dᵇ k {k<j} = A .Dᵇ k {<ᵇ<ᵇ j<i k<j}
((A ↓ᵇ j) {j<i}) .τᵇ k {k<j} = A .τᵇ k {<ᵇ<ᵇ j<i k<j}

-- Raw inputs to stage i are terms over any strictly earlier stage.
Wᵇ : ∀ {i} → IdxStructᵇ i → Set _
Wᵇ {i} A = Σᵇ i λ j {j<i} → Expr (Dᵇ A j {j<i})

-- Equations, monad units, and monad multiplication generate the stage quotient.
data Rᵇ {i : Size} (A : IdxStructᵇ i) : Wᵇ A → Wᵇ A → Prop _ where
  τεᵇ : ∀ᵇ i λ j {j<i} →
    (e : E)
    → (ρ : Ξ e .Equation.V → Dᵇ A j {j<i})
    → Rᵇ A (pairᵇ j (ExprMap ρ (Ξ e .Equation.lhs)))
           (pairᵇ j (ExprMap ρ (Ξ e .Equation.rhs)))
  τηᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
    (t : Expr (Dᵇ A k {<ᵇ<ᵇ j<i k<j}))
    → Rᵇ A (pairᵇ j (varᴱ (τᵇ A j {j<i} k {k<j} t)))
           (pairᵇ k {<ᵇ<ᵇ j<i k<j} t)
  τσᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
    (s : S)
    → (f : P s → Expr (Dᵇ A k {<ᵇ<ᵇ j<i k<j}))
    → Rᵇ A (pairᵇ k {<ᵇ<ᵇ j<i k<j} (supᴱ s f))
           (pairᵇ j (supᴱ s λ p → varᴱ (τᵇ A j {j<i} k {k<j} (f p))))

-- The next iterated-monad stage (FPS (6.1)).
◇ : ∀ {i} → IdxStructᵇ i → Set _
◇ A = Wᵇ A / Rᵇ A

-- Quotient classes transport coherently when the bounded structure changes.
quotient-transport : ∀ {i} {A B : IdxStructᵇ i} (p : A ≡ B)
  (x : Wᵇ A)
  → subst (λ X → ◇ X) p Q.[ x ]
    ≡ Q.[ subst Wᵇ p x ]
quotient-transport ≡.refl x = ≡.refl

-- A fixed structure identifies every stage with the quotient generated below it.
record FixedPoint (A : IdxStruct) : Set _ where
  field
    stage : ∀ i → D A i ≅ˢ ◇ (A ↓ i)
    τ-β : ∀ i j {j<i} (t : Expr (D A j))
      → stage i .≅ˢ.to  (τ A i j {j<i} t)
      ≡ Q.[ pairᵇ j {j<i} t ]
open FixedPoint public

◇fix : IdxStruct → Set _
◇fix = FixedPoint

FixSizeStruct : Set _
FixSizeStruct = Σ IdxStruct FixedPoint

-- A bounded structure is fixed at every stage strictly below its bound.
isFixSizeStructᵇ : {i : Size} → IdxStructᵇ i → Prop _
isFixSizeStructᵇ A =
  ∀ j {j<i} →
    ∃ λ (p : Box (Dᵇ A j {j<i} ≡ ◇ ((A ↓ᵇ j) {j<i}))) →
      ∀ k {k<j} →
        ∀ t →
          subst (λ X → X) (p .unbox)
            (τᵇ A j {j<i} k {k<j} t)
            ≡ Q.[ pairᵇ k {k<j} t ]

FixSizeStructᵇ : (i : Size) → Set _
FixSizeStructᵇ i = ΣP (IdxStructᵇ i) isFixSizeStructᵇ

-- Restricting a bounded fixed structure yields bounded fixed structures.
FixSizeStructᵇ↓ᵇ : ∀ {i} (A : FixSizeStructᵇ i)
  → Πᵇ i λ j {j<i} → FixSizeStructᵇ j
FixSizeStructᵇ↓ᵇ (A , δ) j {j<i} = (A ↓ᵇ j) , δ↓
  where
  δ↓ : isFixSizeStructᵇ ((A ↓ᵇ j) {j<i})
  δ↓ k {k<j} with δ k {<ᵇ<ᵇ j<i k<j}
  ... | ∃i p , q = ∃i p , λ l {l<k} t → q l {l<k} t

-- Fixed bounded structures are unique at each size.  The proof proceeds by
-- well-founded induction: compare all restrictions first, then use the two
-- fixed-point witnesses to compare domains and transition maps.
FixSizeStructᵇ-uniq :
  (i : Size)
  → (I I' : FixSizeStructᵇ i)
  → I ≡ I'
FixSizeStructᵇ-uniq = wf-rec Z._<_ Z.iswf< M hyp
  where
  M : Size → Prop _
  M i = (I I' : FixSizeStructᵇ i) → I ≡ I'

  hyp : ∀ i → (∀ j → j <ᵇ i → M j) → M i
  hyp i ih (A , δ) (A' , δ') =
    ΣP≡ _ _ (IdxStructᵇ-ext domain-family-eq tau-eq)
    where
    -- Induction hypotheses identify the restrictions at every earlier size.
    restriction-eq : ∀ j {j<i}
      → (A ↓ᵇ j) {j<i} ≡ (A' ↓ᵇ j) {j<i}
    restriction-eq j {j<i} =
      ≡.cong fst
        (ih j j<i
          (FixSizeStructᵇ↓ᵇ (A , δ) j {j<i})
          (FixSizeStructᵇ↓ᵇ (A' , δ') j {j<i}))

    -- The first component of each fixed-point witness identifies domains.
    domain-eq : ∀ j {j<i}
      → Dᵇ A j {j<i} ≡ Dᵇ A' j {j<i}
    domain-eq j {j<i} with δ j {j<i} | δ' j {j<i}
    ... | ∃i p , _ | ∃i p' , _ =
      ≡.trans (p .unbox)
        (≡.trans
          (≡.cong ◇ (restriction-eq j {j<i}))
          (≡.sym (p' .unbox)))

    domain-family-eq : Dᵇ A ≡ Dᵇ A'
    domain-family-eq =
      funExt λ j → funExtip λ p → domain-eq j {j<i = p}

    -- The second component identifies transition maps after transporting
    -- expressions and quotient representatives along domain-family-eq.
    tau-eq :
      subst (λ X → τᵇ-type i X) domain-family-eq (τᵇ A)
        ≡ τᵇ A'
    tau-eq =
      funExt λ j → funExtip λ p → funExt λ k → funExtip λ q →
        funExt λ t → {!!}

-- Contractibility packages existence and uniqueness so that the
-- proposition-only well-founded recursor can define a Set-valued family.
FixSizeStructᵇ-contractible : ∀ i → isContr (FixSizeStructᵇ i)
FixSizeStructᵇ-contractible = wf-rec Z._<_ Z.iswf< C hyp
  where
  C : Size → Prop _
  C i = isContr (FixSizeStructᵇ i)

  hyp : ∀ i → (∀ j → j <ᵇ i → C j) → C i
  hyp i ih = ∃i candidate , λ I → FixSizeStructᵇ-uniq i candidate I
    where
    -- Choose the recursively constructed fixed point at every predecessor.
    prev : Πᵇ i λ j {j<i} → FixSizeStructᵇ j
    prev j {j<i} = A!C.a!c a!c* (FixSizeStructᵇ j) (ih j j<i)

    domi : Dᵇ-type i
    domi j {j<i} = ◇ ((prev j {j<i}) .fst)

    -- Every earlier domain can be identified with the corresponding domain
    -- in the fixed point chosen at the current predecessor.
    domi< : ∀ j {j<i} k {k<j}
      → domi k {<ᵇ<ᵇ j<i k<j}
        ≡ Dᵇ ((prev j {j<i}) .fst) k {k<j}
    domi< j {j<i} k {k<j} with
      (prev j {j<i}) .snd k {k<j}
    ... | ∃i p , _ =
      ≡.trans
        (≡.cong ◇
          (≡.cong fst
            (FixSizeStructᵇ-uniq k
              (prev k {<ᵇ<ᵇ j<i k<j})
              (FixSizeStructᵇ↓ᵇ (prev j {j<i}) k {k<j}))))
        (≡.sym (p .unbox))

    τi : τᵇ-type i domi
    τi j {j<i} k {k<j} t = {!!}

    Di : IdxStructᵇ i
    Di = mkIdxStructᵇ domi τi

    Di↓ᵇ : ∀ j {j<i} → (Di ↓ᵇ j) {j<i} ≡ (prev j {j<i}) .fst
    Di↓ᵇ j {j<i} = {!!}

    δi : isFixSizeStructᵇ Di
    δi j {j<i} = {!!}

    -- Construct the quotient stage from the canonical fixed points below i.
    candidate : FixSizeStructᵇ i
    candidate = Di , δi

-- The bounded recursive family of fixed stages.
initᵇ : ∀ i → FixSizeStructᵇ i
initᵇ i = A!C.a!c a!c* (FixSizeStructᵇ i) (FixSizeStructᵇ-contractible i)

-- The global fixed point is assembled from the bounded family.  The remaining
-- holes are the coherent transport of domains and quotient representatives.
init : FixSizeStruct
init = {!!}
