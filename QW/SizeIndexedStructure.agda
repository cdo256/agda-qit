module QW.SizeIndexedStructure where

open import QW.ColimitsOfSizedIndexedDiagrams public

----------------------------------------------------------------------
-- Size-indexed structures for a signature Σ and system of equations ε
-- (Definitions 6.2 and 6.3)
----------------------------------------------------------------------
module SizeIdxStruct
  {ℓ : Level}
  (Σ : Sig {ℓ})
  (ε : Syseq Σ)
  -- We give the definition for an arbitrary type of sizes; later on
  -- this gets instantiated with a type of sizes associated with Σ,ε
  -- whose existence is given by Theorem 5.6
  -- (CocontinuityOfTakingPowers)
  (Size : Set ℓ)
  {{ssz : SizeStructure Size}}
  where
  private
    Γ = fst ε
    lhs = fst (snd ε)
    rhs = snd (snd ε)
  open Colim Size {{ssz}}

  -- Definition 6.2
  record IdxStruct : Set (lsuc ℓ) where
    constructor mkIdxStruct
    field
      D : Size → Set ℓ -- D aka dom
      τ : ∀ i → ∏ᵇ i λ j {j<i} → (T{ℓ}{Σ}(D j) → D i)
  open IdxStruct public

  -- (↓ i)-indexed structure (i : Size),
  -- i.e. indexed for all j : Size and j < i
  Dᵇ-type : (i : Size) → Set (lsuc ℓ) 
  Dᵇ-type i =
      ∏ᵇ i λ j {j<i}
    → Set ℓ
  τᵇ-type : (i : Size) → (Dᵇ : Dᵇ-type i) → Set ℓ
  τᵇ-type i Dᵇ =
      ∏ᵇ i λ j {j<i}
    → ∏ᵇ j λ k {k<j}
    → (T{ℓ}{Σ}(Dᵇ k {<ᵇ<ᵇ j<i k<j}) → Dᵇ j {j<i})
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

  Wᵇ : ∀{i} → IdxStructᵇ i → Set ℓ
  Wᵇ {i} A = ∑ᵇ i λ j {j<i} → T{ℓ}{Σ} (Dᵇ A j {j<i})

  -- (6.2)
  data Rᵇ {i : Size}(A : IdxStructᵇ i) : Wᵇ A → Wᵇ A → Prop ℓ where
    τεᵇ : ∀ᵇ i λ j {j<i} →
      ((e : Op Γ)
        (ρ : Ar Γ e → Dᵇ A j {j<i})
        → ----------------------------------------------------
        Rᵇ A (pairᵇ j (T' ρ (lhs e))) (pairᵇ j (T' ρ (rhs e))))
    τηᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → 
      ((t : T{ℓ}{Σ}(Dᵇ A k))
        → ------------------------------------------
        Rᵇ A (pairᵇ j {j<i} (η (τᵇ A j {j<i} k {k<j} t))) (pairᵇ k {<ᵇ<ᵇ j<i k<j} t))
    τσᵇ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
      ((a : Op Σ)
        (f : Ar Σ a → T (Dᵇ A k))
        → ------------------------------------------------
        Rᵇ A (pairᵇ k {<< j<i k<j} (σ (a , f)))
            (pairᵇ j {j<i} (σ (a , λ b → η (τᵇ A j {j<i} k {k<j} (f b))))))

  -- (6.1)
  ◇ : ∀{i} → IdxStructᵇ i → Set ℓ
  ◇ A = Wᵇ A / Rᵇ A

  -- Definition 6.3
  ◇fix : IdxStruct → Prop (lsuc ℓ)
  ◇fix alg =
    ∀ i → D alg i == ◇ (alg ↓ i) ∧
    ∀ᵇ i λ j {j<i} → (∀ t → τ alg i j {j<i} t === [ pairᵇ j {j<i} t ]/ Rᵇ (alg ↓ i))

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
      ∀ᵇ i λ j {j<i} → (Dᵇ alg j {j<i} == ◇ ((alg ↓ᵇ j) {j<i})
        ∧ ∀ᵇ j λ k {k<j} → 
          ((t : T{ℓ}{Σ}(Dᵇ (mkIdxStructᵇ (Dᵇ alg) (τᵇ alg)) k))
            → τᵇ alg j {j<i} k {k<j} t === [ pairᵇ k {k<j} t ]/ Rᵇ ((alg ↓ᵇ j) {j<i})
          )
      )
