module QW.Size where

open import WellFoundedRelations public
open import WeaklyInitialSetsOfCovers public
open import QW.IndexedPolynomialFunctorsAndEquationalSystems public

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
  record _<ᵇ_  (i j : Size) : Prop l where
    constructor <inst
    field <prf : i < j
  open _<ᵇ_ public

  <ᵇ<ᵇ :
    {i j k : Size}
    {q : j <ᵇ k}
    {p : i <ᵇ j}
    → ------------------------
    i <ᵇ k
  <ᵇ<ᵇ {q = q} {p = p} = <inst (<< (<prf q) (<prf p))

  <ᵇ∨ˢl : {i : Size}(j : Size) → i <ᵇ i ∨ˢ j
  <ᵇ∨ˢl j = <inst (<∨ˢl j)

  <ᵇ∨ˢr : (i : Size){j : Size} → j <ᵇ i ∨ˢ j
  <ᵇ∨ˢr i = <inst (<∨ˢr i)

  <ᵇ↑ˢ : {i : Size} → i <ᵇ ↑ˢ i
  <ᵇ↑ˢ = <inst (<↑ˢ)

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
∏ᵇ {l} {Size} i B = (j : Size){j<i : j <ᵇ i} → B j {j<i}

infix 2 ∏ᵇsyntax

∏ᵇsyntax :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (B : (j : Size){_ : j <ᵇ i} → Set m)
  → ------------------------------------
  Set (l ⊔ m)
∏ᵇsyntax = ∏ᵇ
syntax ∏ᵇsyntax i (λ j → B) = ∏ᵇ j < i , B

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
∀ᵇ i P =  ∀ j  → {j<i : j <ᵇ i} → P j {j<i}

∀ᵇsyntax :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (P : (j : Size){_ : j <ᵇ i} → Prop m)
  → -------------------------------------
  Prop (l ⊔ m)
∀ᵇsyntax = ∀ᵇ
syntax ∀ᵇsyntax i (λ j → P) = ∀ᵇ j < i , P

funᵇ-ext :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  {i : Size}
  {m : Level}
  {B : (j : Size){_ : j <ᵇ i} → Set m}
  {f f' : (j : Size){j<i : j <ᵇ i} → B j {j<i}}
  (_ : (j : Size){j<i : j <ᵇ i} → (f j {j<i} == f' j {j<i}))
  → ------------------------------------
  f == f'
funᵇ-ext e =
  funext λ j →
  {!instance-funexp λ p → e j {p}!}

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

infix 2 Σᵇsyntax

Σᵇsyntax :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (B : (j : Size){_ : j <ᵇ i} → Set m)
  → ------------------------------------
  Set (l ⊔ m)
Σᵇsyntax = ∑ᵇ
syntax Σᵇsyntax i (λ j → B) = ∑ᵇ j < i , B

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

infix 2 ∃ᵇsyntax

∃ᵇsyntax :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  (i : Size)
  {m : Level}
  (P : (j : Size){_ : j <ᵇ i} → Prop m)
  → -------------------------------------
  Prop (l ⊔ m)
∃ᵇsyntax = ∃ᵇ
syntax ∃ᵇsyntax i (λ j → P) = ∃ᵇ j < i , P

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
    {{ins<}} : ins <ᵇ i
    prf      : P ins
open subsetᵇ public

syntax subsetᵇ i (λ j → P) = subsetᵇ j < i , P

----------------------------------------------------------------------
-- Bounded well-founded induction and recursion (Proposition 5.3)
----------------------------------------------------------------------
<ind :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  {n : Level}
  (P : Size → Prop n)
  (p : ∀ i → (∀ᵇ j < i , P j) → P i)
  → --------------------------------
  ∀ i → P i
<ind P p = wf.ind _<_ <iswf P
  (λ i h → p i (λ j {j<i} → h j (<prf j<i)))

<rec :
  {l : Level}
  {Size : Set l}
  {{_ : SizeStructure Size}}
  {n : Level}
  (B : Size → Set n)
  (b : ∀ i → (∏ᵇ j < i , B j) → B i)
  → --------------------------------
  ∀ i → B i
<rec B b = wf.rec _<_ <iswf B
  (λ i h → b i (λ j {j<i} → h j (<prf j<i)))

----------------------------------------------------------------------
-- Plump order (Example 5.4)
----------------------------------------------------------------------
module Plump {l : Level}(Σ : Sig{l}) where
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
-- The size associated with a signature (Lemma 5.5)
----------------------------------------------------------------------
SizeSig : {l : Level} → Sig{l} → Sig{l}
-- SizeSig Σ is the signature Σ augmented with
-- a nullary and a binary operation
Op (SizeSig {l} Σ) = 𝟙 + 𝟙 + Op Σ
Ar (SizeSig {l} Σ) (ι₁ _)      = 𝟘
Ar (SizeSig {l} Σ) (ι₂ (ι₁ _)) = Unit{l} + Unit{l}
Ar (SizeSig {l} Σ) (ι₂ (ι₂ a)) = Ar Σ a

Sz : {l : Level} → Sig{l} → Set l
-- Sz Σ is the underlying set of the type of sizes associated with Σ
Sz Σ = 𝕎 (SizeSig Σ)

-- Sz Σ is a type of sizes:
module _ {l : Level}{Σ : Sig{l}} where
  instance
    SizeStructureSize : SizeStructure (Sz Σ)
    SizeStructureSize = record
      { _<_ = _≺_
      ; << = ≺≺
      ; <iswf = iswf≺
      ; Oˢ = σ (ι₁ _ , λ ())
      ; _∨ˢ_ = λ i  j → σ (ι₂ (ι₁ _) , (λ{(ι₁ _) → i ; (ι₂ _) → j}))
             ; <∨ˢl = λ _ → ≺sup (ι₁ _) (≤refl _)
      ; <∨ˢr = λ _ → ≺sup (ι₂ _) (≤refl _)
      }
      where
      open Plump (SizeSig Σ)

record UpperBounds
-- Upper bounds in the type of sizes Sz Ξ
-- for families indexed by arities in Σ
  {l : Level}
  (Σ : Sig {l})
  (Ξ : Sig {l})
  : Set (lsuc l)
  where
  field
    ⋁ˢ :
      (a : Op Σ)
      (f : Ar Σ a → Sz Ξ)
      → -------------------
      Sz Ξ
    <⋁ˢ :
      {a : Op Σ}
      (f : Ar Σ a → Sz Ξ)
      (x : Ar Σ a)
      → -----------------
      f x < ⋁ˢ a f
    <ᵇ⋁ˢ :
      {a : Op Σ}
      (f : Ar Σ a → Sz Ξ)
      (x : Ar Σ a)
      → -------------------
      f x <ᵇ ⋁ˢ a f
    -- ↑ˢ< : {i j : Sz Ξ} → i < j → ↑ˢ i < ↑ˢ j
    -- ↑ˢ<ᵇ : {i j : Sz Ξ} →  i <ᵇ j → ↑ˢ i <ᵇ ↑ˢ j
open UpperBounds{{...}} public

-- The type of sizes for a signature Σ has upper bounds for
-- families index by arities in Σ
module _ {l : Level}{Σ : Sig{l}} where
  open Plump (SizeSig Σ)
  instance
    UpperBoundsSize : UpperBounds {l} Σ Σ
    ⋁ˢ   {{UpperBoundsSize}} a f       = sup (ι₂ (ι₂ a) , f)
    <⋁ˢ  {{UpperBoundsSize}} f x       = ≺sup x (≤refl (f x))
    <ᵇ⋁ˢ {{UpperBoundsSize}} f x       = <inst (<⋁ˢ f x)
