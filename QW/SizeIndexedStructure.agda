module QW.SizeIndexedStructure where

open import QW.ColimitsOfSizedIndexedDiagrams public

----------------------------------------------------------------------
-- Size-indexed structures for a signature Σ and system of equations ε
-- (Definitions 6.2 and 6.3)
----------------------------------------------------------------------
module SizeIdxStruct
  {l : Level}
  (Σ : Sig {l})
  (ε : Syseq Σ)
  -- We give the definition for an arbitrary type of sizes; later on
  -- this gets instantiated with a type of sizes associated with Σ,ε
  -- whose existence is given by Theorem 5.6
  -- (CocontinuityOfTakingPowers)
  (Size : Set l)
  {{ssz : SizeStructure Size}}
  where
  private
    Γ = fst ε
    lhs = fst (snd ε)
    rhs = snd (snd ε)
  open Colim Size {{ssz}}

  -- Definition 6.2
  record IdxStruct : Set (lsuc l) where
    constructor mkIdxStruct
    field
      D : Size → Set l -- D aka dom
      τ : ∀ i → ∏ᵇ j < i , (T{l}{Σ}(D j) → D i)
  open IdxStruct public

  -- (↓ i)-indexed structure (i : Size),
  -- i.e. indexed for all j : Size and j < i
  record IdxStructᵇ (i : Size) : Set (lsuc l) where
    constructor mkIdxStructᵇ
    field
      Dᵇ : ∏ᵇ j < i , Set l
      τᵇ : ∏ᵇ j < i , ∏ᵇ k < j , (T{l}{Σ}(Dᵇ k) → Dᵇ j)
  open IdxStructᵇ public

  infixl 6 _↓_
  -- restriction of a (any) Size-indexed alg to a (↓ i)-indexed alg
  _↓_ : IdxStruct → ∀ i → IdxStructᵇ i
  Dᵇ (A ↓ i) j   = D A j
  τᵇ (A ↓ i) j k = τ A j k

  infixl 6 _↓ᵇ_
  -- restriction of a (↓ i)-indexed alg to a (↓ j)-indexed alg,
  -- when j < i
  _↓ᵇ_ : {i : Size} → IdxStructᵇ i → ∏ᵇ j < i , IdxStructᵇ j
  Dᵇ (A ↓ᵇ _) j  = Dᵇ A j
  τᵇ (A ↓ᵇ _) j k = τᵇ A j k

  Wᵇ : ∀{i} → IdxStructᵇ i → Set l
  Wᵇ {i} A = ∑ᵇ j < i , T{l}{Σ} (Dᵇ A j)

  -- (6.2)
  data Rᵇ {i : Size}(A : IdxStructᵇ i) : Wᵇ A → Wᵇ A → Prop l where
    τεᵇ : ∀ᵇ j < i ,
      ((e : Op Γ)
        (ρ : Ar Γ e → Dᵇ A j)
        → ----------------------------------------------------
        Rᵇ A (pairᵇ j (T' ρ (lhs e))) (pairᵇ j (T' ρ (rhs e))))
    τηᵇ : ∀ᵇ j < i , ∀ᵇ k < j ,
      ((t : T{l}{Σ}(Dᵇ A k))
        → ------------------------------------------
        Rᵇ A (pairᵇ j (η (τᵇ A j k t))) (pairᵇ k t))
    τσᵇ : ∀ᵇ j < i , ∀ᵇ k < j ,
      ((a : Op Σ)
        (f : Ar Σ a → T (Dᵇ A k))
        → ------------------------------------------------
        Rᵇ A (pairᵇ k (σ (a , f)))
            (pairᵇ j (σ (a , λ b → η (τᵇ A j k (f b))))))

  -- (6.1)
  ◇ : ∀{i} → IdxStructᵇ i → Set l
  ◇ A = Wᵇ A / Rᵇ A

  -- Definition 6.3
  ◇fix : IdxStruct → Prop (lsuc l)
  ◇fix alg =
    ∀ i → D alg i == ◇ (alg ↓ i) ∧
    ∀ᵇ j < i , (∀ t → τ alg i j t === [ pairᵇ j t ]/ Rᵇ (alg ↓ i))

  -- We will show (Proposition 6.4) that any element of the folowing
  -- type yields an initial algebra for the equational systen (Σ,ε)
  -- when Size,ssz is instantiated with a suitable type of sizes
  FixSizeStruct : Set (lsuc l)
  FixSizeStruct = set IdxStruct ◇fix

  -- To actually construct an element of FixSizeStruct we will use
  -- well-founded recursion to construct an element of the following
  -- size-indexed family and then take its colimit (Theorem 6.1)
  FixSizeStructᵇ : Size → Set (lsuc l)
  FixSizeStructᵇ i = set (IdxStructᵇ i) isFixSizeStructᵇ
    module _ where
    isFixSizeStructᵇ : IdxStructᵇ i → Prop (lsuc l)
    isFixSizeStructᵇ alg =
      ∀ᵇ j < i , (Dᵇ alg j == ◇ (alg ↓ᵇ j)
        ∧ ∀ᵇ k < j ,
          ((t : T{l}{Σ}(Dᵇ (mkIdxStructᵇ (Dᵇ alg) (τᵇ alg)) k))
            → τᵇ alg j k t === [ pairᵇ k t ]/ Rᵇ (alg ↓ᵇ j)
          )
      )
