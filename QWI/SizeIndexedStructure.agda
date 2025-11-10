module QWI.SizeIndexedStructure where

open import QWI.ColimitsOfSizedIndexedDiagrams public

----------------------------------------------------------------------
-- Size-indexed structures for an indexed signature Σ (3.26)
-- and system of equations ε (3.31)
----------------------------------------------------------------------
module SizeIdxStruct
  {l : Level}
  (I : Set l)
  (Σ : Slice.Sig I)
  (ε : Slice.Syseq I Σ)
  -- We give the definition for an arbitrary type of sizes; later on
  -- this gets instantiated with a type of sizes associated with Σ,ε
  -- whose existence is given by Theorem 5.6
  -- (CocontinuityOfTakingPowers)
  (Size : Set l)
  {{ssz : SizeStructure Size}}
  where
  open Slice I

  private
    Γ = Syseq.Γ ε
    lhs = Syseq.lhs ε
    rhs = Syseq.rhs ε

  open Colim Size {{ssz}}

  -- Definition 6.2
  record IdxStruct : Set (lsuc l) where
    constructor mkIdxStruct
    field
      D : Size → Setᴵ l -- D aka dom
      τ : ∀ i → ∏ᵇ j < i , (T{Σ}(D j) ⇁ D i)
  open IdxStruct public

  -- (↓ i)-indexed structure (i : Size),
  -- i.e. indexed for all j : Size and j < i
  record IdxStructᵇ (i : Size) : Set (lsuc l) where
    constructor mkIdxStructᵇ
    field
      Dᵇ : ∏ᵇ j < i , Setᴵ l
      τᵇ : ∏ᵇ j < i , ∏ᵇ k < j , (T{Σ}(Dᵇ k) ⇁ Dᵇ j)
  open IdxStructᵇ public

  infixl 6 _↓_
  -- restriction of a (any) Size-indexed alg to a (↓ i)-indexed alg
  _↓_ : IdxStruct → ∀ i → IdxStructᵇ i
  Dᵇ (A ↓ _) j   = D A j
  τᵇ (A ↓ _) j k = τ A j k

  infixl 6 _↓ᵇ_
  -- restriction of a (↓ i)-indexed alg to a (↓ j)-indexed alg,
  -- when j < i
  _↓ᵇ_ : {i : Size} → IdxStructᵇ i → ∏ᵇ j < i , IdxStructᵇ j
  Dᵇ (A ↓ᵇ _) j  = Dᵇ A j
  τᵇ (A ↓ᵇ _) j k = τᵇ A j k

  Wᵇ : ∀{i} → IdxStructᵇ i → Setᴵ l
  Wᵇ {i} A n = ∑ᵇ j < i , T{Σ} (Dᵇ A j) n

  -- (6.2)
  data Rᵇ
    {i : Size}
    (A : IdxStructᵇ i)
    (n : I)
    : ----------------------
    Wᵇ A n → Wᵇ A n → Prop l
    where
    τεᵇ : ∀ᵇ j < i ,
      ((e : Op Γ n)
       (ρ : Ar Γ n e ⇁ Dᵇ A j)
        → ---------------------------------------------------------------
        Rᵇ A n (pairᵇ j (T' ρ n (lhs n e))) (pairᵇ j (T' ρ n (rhs n e))))
    τηᵇ : ∀ᵇ j < i , ∀ᵇ k < j ,
      ((t : T{Σ}(Dᵇ A k) n)
        → ------------------------------------------
        Rᵇ A n (pairᵇ j (η n (τᵇ A j k n t))) (pairᵇ k t))
    τσᵇ : ∀ᵇ j < i , ∀ᵇ k < j ,
      ((a : Op Σ n)
        (f : Ar Σ n a ⇁ T (Dᵇ A k))
        → ------------------------------------------------
        Rᵇ A n (pairᵇ k (σ n (a , f)))
            (pairᵇ j (σ n (a , λ m b → η m (τᵇ A j k m (f m b))))))

  -- (6.1)
  ◇ : ∀{i} → IdxStructᵇ i → Setᴵ l
  ◇ A n = Wᵇ A n / Rᵇ A n

  -- Definition 6.3
  ◇fix : IdxStruct → Prop (lsuc l)
  ◇fix alg =
    ∀ i → (∀ n → D alg i n == ◇ (alg ↓ i) n) ∧
    ∀ᵇ j < i , (∀ n t → τ alg i j n t === [ pairᵇ j t ]/ Rᵇ (alg ↓ i) n)

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
      ∀ᵇ j < i , ((∀ n → Dᵇ alg j n == ◇ (alg ↓ᵇ j) n)
        ∧ ∀ᵇ k < j ,
          ((n : I)
          (t : T {Σ} (Dᵇ (mkIdxStructᵇ (Dᵇ alg) (τᵇ alg)) k) n)
          → ---------------------------------------------------
          τᵇ alg j k n t === [ pairᵇ k t ]/ Rᵇ (alg ↓ᵇ j) n    ))
