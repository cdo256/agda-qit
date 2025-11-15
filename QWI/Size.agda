{-#  OPTIONS --prop --rewriting --show-irrelevant #-}

module QWI.Size where

open import WellFoundedRelations public
open import WeaklyInitialSetsOfCovers public
open import QWI.IndexedPolynomialFunctorsAndEquationalSystems public

----------------------------------------------------------------------
-- Definition 5.1 (Size)
----------------------------------------------------------------------
record SizeStructure {l : Level} (Size : Set l) : Set (lsuc l) where
  infix  4 _<_
  infixr 6 _∨ˢ_
  field
    _<_   : Size → Size → Prop l
    <<    : ∀{i j k} → j < k → i < j → i < k
    <iswf : wf.iswf _<_
    Oˢ    : Size
    _∨ˢ_  : Size → Size → Size
    <∨ˢl  : ∀{i} j  → i < i ∨ˢ j
    <∨ˢr  : ∀ i {j} → j < i ∨ˢ j
  ↑ˢ : Size → Size
  ↑ˢ i = i ∨ˢ i
  <↑ˢ : ∀{i} → i < ↑ˢ i
  <↑ˢ {i} = <∨ˢl i
open SizeStructure{{...}} public

{-# DISPLAY SizeStructure._<_  _ i j = i < j  #-}
{-# DISPLAY SizeStructure._∨ˢ_ _ i j = i ∨ˢ j #-}

----------------------------------------------------------------------
-- Bounded quantification over sizes (Notation 5.2)
----------------------------------------------------------------------

-- Use instance search for transitivity proofs about <
module _ {l : Level}{Size : Set l}{{_ : SizeStructure Size}} where
  infix 4 _<ᵇ_
  _<ᵇ_ : Size → Size → Prop l
  _<ᵇ_ = _<_

  <ᵇ<ᵇ :
    {i j k : Size}
    (q : j <ᵇ k)
    (p : i <ᵇ j)
    → ------------------------
    i <ᵇ k
  <ᵇ<ᵇ q p = << q p

  <ᵇ∨ˢl : {i : Size}(j : Size) → i <ᵇ i ∨ˢ j
  <ᵇ∨ˢl j = <∨ˢl j

  <ᵇ∨ˢr : (i : Size){j : Size} → j <ᵇ i ∨ˢ j
  <ᵇ∨ˢr i = <∨ˢr i

  <ᵇ↑ˢ : {i : Size} → i <ᵇ ↑ˢ i
  <ᵇ↑ˢ = <↑ˢ

-- Bounded dependent function
∏ᵇ :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (B : (j : Size){_ : j <ᵇ i} → Set m)
  → ------------------------------------
  Set (l ⊔ m)
∏ᵇ {l} {Size} i B = ∀ j {j<i : j <ᵇ i} → B j {j<i}

-- Bounded universal quantification
∀ᵇ :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (P : (j : Size){_ : j <ᵇ i} → Prop m)
  → -------------------------------------
  Prop (l ⊔ m)
∀ᵇ i P = ∀ j {j<i : j <ᵇ i} → P j {j<i}

funᵇ-ext :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  {i : Size}
  {m : Level}
  {B : (j : Size){_ : j <ᵇ i} → Set m}
  {f f' : (j : Size){j<i : j <ᵇ i} → B j {j<i}}
  (eq : (j : Size){j<i : j <ᵇ i} → (f j {j<i} == f' j {j<i}))
  → ------------------------------------
  f == f'
funᵇ-ext {Size = Size} {i = i} {B = B} {f = f} {f' = f'} eq =
  funext (λ j → implicit-funexp λ x → eq j)

-- Bounded dependent product
record ∑ᵇ
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (B : (j : Size){_ : j <ᵇ i} → Set m)
  : ------------------------------------
  Set (l ⊔ m)
  where
  constructor pairᵇ
  field
    fst      : Size
    {fst<} : fst <ᵇ i
    snd      : B fst {fst<}
open ∑ᵇ public

-- Bounded existential quantification
data ∃ᵇ
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (P : (j : Size){_ : j <ᵇ i} → Prop m)
  : -------------------------------------
  Prop (l ⊔ m)
  where
    ∃ᵇi : (j : Size){j<i : j <ᵇ i} → P j {j<i} → ∃ᵇ i P

-- Bounded comprehension
infixl 4 _∣ᵇ_
record subsetᵇ
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (P : Size → Prop m)
  : --------------
  Set (l ⊔ m)
  where
  constructor _∣ᵇ_
  field
    ins      : Size
    {ins<} : ins <ᵇ i
    prf      : P ins
open subsetᵇ public

----------------------------------------------------------------------
-- Bounded well-founded induction and recursion (Proposition 5.3)
----------------------------------------------------------------------
<ind :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  {n : Level}
  (P : Size → Prop n)
  (p : ∀ i → (∀ j {j<i : j <ᵇ i} → P j) → P i)
  → --------------------------------
  ∀ i → P i
<ind P p = wf.ind _<_ <iswf P
  (λ i h → p i (λ j {j<i} → h j j<i))

<rec :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  {n : Level}
  (B : Size → Set n)
  (b : ∀ i → (∀ j → {_ : j <ᵇ i} → B j) → B i)
  → --------------------------------
  ∀ i → B i
<rec B b = wf.rec _<_ <iswf B
  (λ i h → b i (λ j {j<i} → h j j<i))

----------------------------------------------------------------------
-- Plump order (Example 5.4)
----------------------------------------------------------------------
module Plump {l : Level}(Σ : Unindexed.Sig {l}) where
  open Unindexed {l}

  Size : Set l
  Size = 𝕎 Σ

  -- The well-founded order (<) on Size
  mutual
    infix 4 _≤_ _≺_
    data _≤_ : Size → Size → Prop l where
      sup≤ :
        {a   : Op Σ}
        {f   : Ar Σ a → Size}
        {i   : Size}
        (f<i : ∀ x → f x ≺ i)
        → ---------------------
        sup (a , f) ≤ i
    data _≺_ : Size → Size → Prop l where
      ≺sup :
        {a    : Op Σ}
        {f    : Ar Σ a → Size}
        (x    : Ar Σ a)
        {i    : Size}
        (i≤fx : i ≤ f x)
        → ----------------------
        i ≺ sup (a , f)
  -- ≤ is reflexive
  ≤refl : ∀ i → i ≤ i
  ≤refl (σ (_ , f)) = sup≤ λ x → ≺sup x (≤refl (f x))

  -- Transitivity
  mutual
    ≤≤ : {i j k : Size} → j ≤ k → i ≤ j → i ≤ k
    ≤≤ j≤k (sup≤ f<i) = sup≤ λ x → ≤< j≤k (f<i x)

    -- Could not get the proof of this to go through when
    -- defining Unindexed.W {l} Σ = Slice.W {l} Unit Σ' unit
    ≤< : {i j k : Size} → j ≤ k → i ≺ j → i ≺ k
    ≤< (sup≤ f<i) (≺sup x i≤fx) = <≤ (f<i x) i≤fx

    <≤ : {i j k : Size} → j ≺ k → i ≤ j → i ≺ k
    <≤ (≺sup x i≤fx) i≤j = ≺sup x (≤≤ i≤fx i≤j)
  -- end mutual ------------------------------------------------------

  <→≤ : ∀{i j} → i ≺ j → i ≤ j
  <→≤ (≺sup x (sup≤ f<i)) = sup≤ (λ y → ≺sup x (<→≤ (f<i y)))

  ≺≺ : ∀{i j k} → j ≺ k → i ≺ j → i ≺ k
  ≺≺ (≺sup x i≤fx) i<j = ≺sup x (<→≤ (≤< i≤fx i<j))

  -- Well-foundedness of ≺
  iswf≺ : wf.iswf _≺_
  iswf≺ i = wf.acc λ j j<i → α i j (<→≤ j<i)
    where
    α : ∀ i j → j ≤ i → wf.Acc _≺_ j
    α (σ(_ , f)) j j≤i = wf.acc α'
      where
      α' : ∀ k → k ≺ j → wf.Acc _≺_ k
      α' k k<j with ≤< j≤i k<j
      ... | ≺sup x k≤fx = α (f x) k k≤fx

----------------------------------------------------------------------
-- The size associated with an unindexed signature (Lemma 5.5)
----------------------------------------------------------------------
SizeSig : {l : Level} → Unindexed.Sig {l} → Unindexed.Sig {l}
-- SizeSig Σ is essentially the signature Σ augmented with
-- a nullary and a binary operation
Unindexed.Op (SizeSig {l} Σ) = 𝟙 + 𝟙 + Unindexed.Op Σ
Unindexed.Ar (SizeSig {l} Σ) (ι₁ _) = 𝟘
Unindexed.Ar (SizeSig {l} Σ) (ι₂ (ι₁ _)) = Unit {l} + Unit {l}
Unindexed.Ar (SizeSig {l} Σ) (ι₂ (ι₂ a)) = Unindexed.Ar Σ a

Sz : {l : Level} → Unindexed.Sig → Set l
-- Sz Σ is the underlying set of the type of sizes associated
-- with the indexed signature Σ
Sz Σ = Unindexed.𝕎 (SizeSig Σ)

-- Sz Σ is a type of sizes:
module _ {l : Level}{Σ : Unindexed.Sig{l}} where
  instance
    SizeStructureSize : SizeStructure (Sz Σ)
    SizeStructureSize = record
      { _<_ = _≺_
      ; << = ≺≺
      ; <iswf = iswf≺
      ; Oˢ = Unindexed.σ (ι₁ _ , λ ())
      ; _∨ˢ_ = λ i  j → Unindexed.σ (ι₂ (ι₁ _) , (λ{(ι₁ _) → i ; (ι₂ _) → j}))
             ; <∨ˢl = λ _ → ≺sup (ι₁ _) (≤refl _)
      ; <∨ˢr = λ _ → ≺sup (ι₂ _) (≤refl _)
      }
      where
      open Plump (SizeSig Σ)

  record UpperBounds
  -- Upper bounds in the type of sizes Sz Σ
  -- for families indexed by arities in Ξ
    (Ξ : Unindexed.Sig {l})
    : Set (lsuc l)
    where
    field
      ⋁ˢ :
        (a : Unindexed.Op Ξ)
        (f : Unindexed.Ar Ξ a → Sz Σ)
        → ---------------------------
        Sz Σ
      <⋁ˢ :
        {a : Unindexed.Op Ξ}
        (f : Unindexed.Ar Ξ a → Sz Σ)
        (x : Unindexed.Ar Ξ a)
        → ---------------------------
        f x < ⋁ˢ a f
      <ᵇ⋁ˢ :
        {a : Unindexed.Op Ξ}
        (f : Unindexed.Ar Ξ a → Sz Σ)
        (x : Unindexed.Ar Ξ a)
        → --------------------------
        f x <ᵇ ⋁ˢ a f
  open UpperBounds{{...}} public

  -- The type of sizes for an indexed signature Σ has upper bounds for
  -- families index by arities in Σ
  open Plump (SizeSig Σ)
  module _ where
    instance
      UpperBoundsSize : UpperBounds Σ
      ⋁ˢ   {{UpperBoundsSize}} a f       = Unindexed.sup ((ι₂ (ι₂ a)) , f)
      <⋁ˢ  {{UpperBoundsSize}} f x       = ≺sup x (≤refl (f x))
      <ᵇ⋁ˢ {{UpperBoundsSize}} f x       = <⋁ˢ f x
