{-# OPTIONS --type-in-type #-}
open import QIT.Prelude
open import QIT.QW.Signature
open import QIT.Plump.Algebra
open import QIT.Relation.SetQuotient
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Container.Base
open import QIT.Setoid
open import QIT.Prop

module QIT.QW.Initiality
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (Zᴬ  : PlumpAlgebra (sig .Sig.S) (sig .Sig.P))
  where

open Sig sig
module Z = PlumpAlgebra Zᴬ
open import QIT.Plump.Properties Zᴬ
open import QIT.QW.Diagram sig Zᴬ
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
open import QIT.QW.Stage sig Zᴬ
module F = Functor F
open import QIT.QW.Equation S P

module _
  (cc : FD*/ ≅ˢ F.ob D*/)
  where
  module cc = _≅ˢ_ cc

  open import QIT.QW.Algebra sig
  open import QIT.Algebra.Base
  open import QIT.Colimit.Base ≤p _ _ D̃/

  
  data R : ⟨ D* ⟩ → ⟨ D* ⟩ → Prop _ where
    Rcolim : ∀ x y → x ≈ˡ y → R x y
    Rweaken : ∀ {α β} (p : α Z.≤ β) (x : S̃/ α) → R (α , x) (β , dweaken/ p x)
    Rσ : ∀ {α β} (p : α Z.≤ β) (s : S) (f : P s → S̃/ α)
      → R (β , let u = sup (s , λ i → {!f i!}) in {!!}) (α , {!!})

  Z = Z.Z
  Size = Z.Z
  variable
    ℓ : Level

  _<ᵇ_ : Z → Z → Prop _
  _<ᵇ_ = Z._<_

  Πᵇ : ∀ {ℓB}
    → (α : Z)
    → (B : ∀ β → (β<α : β <ᵇ α) → Set ℓB)
    → Set ℓB
  Πᵇ α B = ∀ β β<α → B β β<α
  ∏ᵇ = Πᵇ

  Σᵇ : ∀ {ℓB}
    → (α : Z)
    → (B : ∀ β → (β<α : β <ᵇ α) → Set ℓB)
    → Set ℓB
  Σᵇ α B = Σ (↓ α) λ (β , β<α) → B β β<α
  ∑ᵇ = Σᵇ

  ∀ᵇ : ∀ {ℓB}
    → (α : Z)
    → (B : ∀ β → (β<α : β <ᵇ α) → Prop ℓB)
    → Prop ℓB
  ∀ᵇ α B = ∀ β β<α → B β β<α

  ∃ᵇ : ∀ {ℓB}
    → (α : Z)
    → (B : ∀ β → (β<α : β <ᵇ α) → Prop ℓB)
    → Prop ℓB
  ∃ᵇ α B = ∃ λ ((β , β<α) : ↓ α) → B β β<α

  Dᵇ-type : ∀ ℓ → (α : Size) → Set (lsuc ℓ) 
  Dᵇ-type ℓ α =
      Πᵇ α λ β β<α → Set _
  τᵇ-type : ∀ {ℓD} (i : Size)
    → (Dᵇ : Dᵇ-type ℓD i)
    → Set ℓD
  τᵇ-type {ℓD} i Dᵇ =
      ∏ᵇ i λ j j<i
    → ∏ᵇ j λ k k<j
    → (Expr ℓD (Dᵇ k (Z.<< j<i k<j)) → Dᵇ j j<i)

  record IdxStruct {ℓD} : Set (lsuc ℓD) where
    constructor mkIdxStruct
    field
      D : Size → Set ℓD -- D aka dom
      τ : ∀ i → Πᵇ i λ j j<i
        → Expr ℓD (D j) → D i
  open IdxStruct public

  record IdxStructᵇ {ℓD} (α : Size) : Set (lsuc ℓD) where
    constructor mkIdxStructᵇ
    field
      Dᵇ : Dᵇ-type ℓD α
      τᵇ : τᵇ-type α Dᵇ
  open IdxStructᵇ public

  infixl 6 _↓_
  -- restriction of a (any) Size-indexed alg to a (↓ i)-indexed alg
  _↓_ : IdxStruct → ∀ i → IdxStructᵇ i
  (A ↓ i) .Dᵇ j j<i = A .D j
    where module A = IdxStruct A
  (A ↓ α) .τᵇ β β<α γ γ<β x = A .τ β γ γ<β x

  infixl 6 _↓ᵇ_
  -- restriction of a (↓ i)-indexed alg to a (↓ j)-indexed alg,
  -- when j < i
  _↓ᵇ_ : {α : Size}
    → IdxStructᵇ α
    → ∀ β (β<α : β <ᵇ α)
    → IdxStructᵇ β
  (A ↓ᵇ β) β<α .Dᵇ γ γ<β = A .Dᵇ γ (Z.<< β<α γ<β)
  (A ↓ᵇ β) β<α .τᵇ γ γ<β = A .τᵇ γ (Z.<< β<α γ<β)

  Wᵇ : ∀ {ℓD} {i} → IdxStructᵇ i → Set ℓD
  Wᵇ {ℓD} {i} A = ∑ᵇ i λ j j<i → Expr ℓD (Dᵇ A j j<i)

  -- (6.2)
  data Rᵇ {ℓ} {i : Size}(A : IdxStructᵇ i) : Wᵇ A → Wᵇ A → Prop ℓ where
    -- Equation
    τεᵇ : ∀ᵇ i λ j j<i
      → (e : E)
      → (ρ : Ξ e .V → Dᵇ A j j<i)
      → Rᵇ A ((j , j<i) , ExprMap ℓ0 ρ (Ξ e .lhs))
             ((j , j<i) , ExprMap ℓ0 ρ (Ξ e .rhs))
    -- Merge free algebras.
    τηᵇ
      : ∀ᵇ i λ j j<i
      → ∀ᵇ j λ k k<j
      → (t : Expr ℓ0 (Dᵇ A k (Z.<< j<i k<j)))
      → Rᵇ A ((j , j<i) , varᴱ (τᵇ A j j<i k k<j t))
             ((k , Z.<< j<i k<j) , t)
    τσᵇ
      : ∀ᵇ i λ j j<i
      → ∀ᵇ j λ k k<j
      → (s : S)
      → (f : P s → Expr ℓ0 (Dᵇ A k (Z.<< j<i k<j)))
      → Rᵇ A ((k , Z.<< j<i k<j) , supᴱ s f)
             ((j , j<i) , supᴱ s λ i → varᴱ (τᵇ A j j<i k k<j (f i)))

  -- (6.1)
  ◇ : ∀{i} → IdxStructᵇ i → Set _
  ◇ A = Wᵇ A / Rᵇ A

{-
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


  FxSzAlg→QWType
    : ∥ SizeIdxStruct.FixSizeStruct Σ ε Size {{ssz}} → QWtype Σ ε ∥


  qw : Record
  qw = record
    (Xα = record
      { alg = mkAlg D*/ ρ
      ; sat = {!!} }
    ; initial = {!!})
    where
    ε₀' : (α : Z.Z) → ⟦ S ◁ P ⟧ (S₀ α) → S₀ (sucᶻ α)
    ε₀' α (s , f) = sup (s , λ i → f i .fst) , Z.sup≤ (λ i → Z.<≤ (<sucᶻ α) (f i .snd))
    ε₀'' : ∀ α s → (f : P s → S̃/ α) → S̃/ (sucᶻ α)
    ε₀'' α s f = {!!}
    ε₀ : ⟨ FD* ⟩ → ⟨ D* ⟩
    ε₀ (α , s , f) = sucᶻ α , {!ε₀'!}
    ε-cong : {!!}
    ε-cong = {!!}
    ε : FD*/ → D*/
    ε = {!!}
    ρ : F.ob D*/ → D*/
    ρ x = ε (cc.from x)
    sup₀ : F.ob ⟨ D* ⟩ → ⟨ D* ⟩
    sup₀ (s , f) = α , {!!}
      where
      α : Z.Z
      α = Z.sup (s , λ i → f i .proj₁)
  
-}
