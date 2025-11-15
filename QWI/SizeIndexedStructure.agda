module QWI.SizeIndexedStructure where

open import QWI.ColimitsOfSizedIndexedDiagrams public

----------------------------------------------------------------------
-- Size-indexed structures for an indexed signature Σ (3.26)
-- and system of equations ε (3.31)
----------------------------------------------------------------------
module SizeIdxStruct
  {ℓ : Level}
  (I : Set ℓ)
  (Σ : Slice.Sig {ℓ} I)
  (ε : Slice.Syseq I Σ)
  -- We give the definition for an arbitrary type of sizes; later on
  -- this gets instantiated with a type of sizes associated with Σ,ε
  -- whose existence is given by Theorem 5.6
  -- (CocontinuityOfTakingPowers)
  (Size : Set ℓ)
  {{ssz : SizeStructure Size}}
  where
  open Slice I

  private
    Γ = Syseq.Γ ε
    lhs = Syseq.lhs ε
    rhs = Syseq.rhs ε

  open Colim Size {{ssz}}

  -- Definition 6.2
  record IdxStruct : Set (lsuc ℓ) where
    constructor mkIdxStruct
    field
      D : Size → Setᴵ ℓ -- D aka dom
      τ : ∀ i → ∏ᵇ i λ j {j<i} → T{Σ}(D j) ⇁ D i 
  open IdxStruct public

  -- (↓ i)-indexed structure (i : Size),
  -- i.e. indexed for all j : Size and j < i
  Dᵇ-type : (i : Size) → Set (lsuc ℓ)
  Dᵇ-type i =
      ∏ᵇ i λ j {j<i}
    → Setᴵ ℓ
  τᵇ-type : (i : Size) → (Dᵇ : Dᵇ-type i) → Set ℓ
  τᵇ-type i Dᵇ =
      ∏ᵇ i λ j {j<i}
    → ∏ᵇ j λ k {k<j}
    → (T{Σ}(Dᵇ k {<ᵇ<ᵇ j<i k<j}) ⇁ Dᵇ j {j<i})
  record IdxStructᵇ (i : Size) : Set (lsuc ℓ) where
    constructor mkIdxStructᵇ
    field
      Dᵇ : Dᵇ-type i
      τᵇ : τᵇ-type i Dᵇ
  open IdxStructᵇ public

  infixl 6 _↓_
  -- restriction of a (any) Size-indexed alg to a (↓ i)-indexed alg
  _↓_ : IdxStruct → ∀ i → IdxStructᵇ i
  Dᵇ (A ↓ i) j = D A j
  τᵇ (A ↓ i) j k {k<j} = τ A j k {k<j}

  infixl 6 _↓ᵇ_
  -- restriction of a (↓ i)-indexed alg to a (↓ j)-indexed alg,
  -- when j < i
  _↓ᵇ_ : {i : Size} → IdxStructᵇ i → ∀ j {j<i : j <ᵇ i} → IdxStructᵇ j
  Dᵇ ((A ↓ᵇ _) {j<i}) k = Dᵇ A k
  τᵇ ((_↓ᵇ_ {i} A j) {j<i}) k {k<j} l {l<k} m = τᵇ A k {j<i = << j<i k<j} l {l<k} m 

  Wᵇ : ∀{i} → IdxStructᵇ i → Setᴵ ℓ
  Wᵇ {i} A n = ∑ᵇ i λ j {j<i} → T{Σ} (Dᵇ A j {j<i}) n

  -- (6.2)
  data Rᵇ
    {i : Size}
    (A : IdxStructᵇ i)
    (n : I)
    : ----------------------
    Wᵇ A n → Wᵇ A n → Prop ℓ
    where
    τεᵇ : ∀ᵇ i λ j {j<i} →
      ((e : Op Γ n)
       (ρ : Ar Γ n e ⇁ Dᵇ A j)
        → ---------------------------------------------------------------
        Rᵇ A n (pairᵇ j (T' ρ n (lhs n e))) (pairᵇ j {j<i} (T' ρ n (rhs n e))))
    τηᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
      ((t : T{Σ}(Dᵇ A k) n)
        → ------------------------------------------
        Rᵇ A n (pairᵇ j {j<i} (η n (τᵇ A j k {k<j} n t))) (pairᵇ k {<ᵇ<ᵇ j<i k<j} t))
    τσᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
      ((a : Op Σ n)
        (f : Ar Σ n a ⇁ T (Dᵇ A k))
        → ------------------------------------------------
        Rᵇ A n (pairᵇ k {<ᵇ<ᵇ j<i k<j} (σ n (a , f)))
            (pairᵇ j {j<i} (σ n (a , λ m b → η m (τᵇ A j k {k<j} m (f m b))))))

  -- (6.1)
  ◇ : ∀{i} → IdxStructᵇ i → Setᴵ ℓ
  ◇ A n = Wᵇ A n / Rᵇ A n

  -- Definition 6.3
  ◇fix : IdxStruct → Prop (lsuc ℓ)
  ◇fix alg =
    ∀ i → (∀ n → D alg i n == ◇ (alg ↓ i) n) ∧
    ∀ᵇ i λ j {j<i} → (∀ n t → τ alg i j {j<i} n t === [ pairᵇ j {j<i} t ]/ Rᵇ (alg ↓ i) n)

  -- We will show (Proposition 6.4) that any element of the folowing
  -- type yields an initial algebra for the equational systen (Σ,ε)
  -- when Size,ssz is instantiated with a suitable type of sizes
  FixSizeStruct : Set (lsuc ℓ)
  FixSizeStruct = set IdxStruct ◇fix

  -- To actually construct an element of FixSizeStruct we will use
  -- well-founded recursion to construct an element of the following
  -- size-indexed family and then take its colimit (Theorem 6.1)
  FixSizeStructᵇ : Size → Set (lsuc ℓ)
  FixSizeStructᵇ i = set (IdxStructᵇ i) isFixSizeStructᵇ
    module _ where
    isFixSizeStructᵇ : IdxStructᵇ i → Prop (lsuc ℓ)
    isFixSizeStructᵇ alg =
      ∀ᵇ i λ j {j<i} → ((∀ n → Dᵇ alg j {j<i} n == ◇ ((alg ↓ᵇ j ) {j<i}) n)
        ∧ ∀ᵇ j λ k {k<j} →
          ((n : I)
          (t : T {Σ} (Dᵇ (mkIdxStructᵇ (Dᵇ alg) (τᵇ alg)) k) n)
          → ---------------------------------------------------
          τᵇ alg j {j<i} k {k<j} n t === [ pairᵇ k {k<j} t ]/ Rᵇ ((alg ↓ᵇ j) {j<i}) n    ))
