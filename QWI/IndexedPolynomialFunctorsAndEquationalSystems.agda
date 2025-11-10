module QWI.IndexedPolynomialFunctorsAndEquationalSystems where

----------------------------------------------------------------------
-- QWI-types (Section 3.3)
----------------------------------------------------------------------

open import TypeTheory public

module Slice
  {l₀ : Level}
  (I : Set l₀)
  where
  -- N.B. We use I as the name of the indexing set, but
  -- n : I, m : I as names for the typical elements
  -- in order to avoid confusion with elements of the,
  -- yet-to-be-defined, Size for some Σ : Sig

  -- objects in the slice category
  Setᴵ : (l₁ : Level) → Set (l₀ ⊔ lsuc l₁)
  Setᴵ l = I → Set l

  ----------------------------------------------------------------------
  -- Slice Category
  ----------------------------------------------------------------------
  infix 4 _⇁_
  _⇁_ : -- (3.23)
    {l₁ l₂ : Level}
    (A : Setᴵ l₁)
    (B : Setᴵ l₂)
    → ----------------
    Set (l₀ ⊔ l₁ ⊔ l₂)
  A ⇁ B = ∀ n → A n → B n

  -- identity in slice category
  idᴵ :
    {l₁ : Level}
    {A : Setᴵ l₁}
    → ---------
    A ⇁ A
  idᴵ n x = x

  -- composition in slice category (3.24)
  _∘ᴵ_ :
    {l₁ l₂ l₃ : Level}
    {A : Setᴵ l₁}
    {B : Setᴵ l₂}
    {C : Setᴵ l₃}
    (g : B ⇁ C)
    (f : A ⇁ B)
    → ------------------
    A ⇁ C
  (g ∘ᴵ f) n = g n ∘ f n

  -- families in slice cateogry (families of Setᴵ indexed by
  -- terms in Setᴵ) (3.25)
  Famᴵ :
    {l₁ : Level}
    (A : Setᴵ l₁)
    (l₂ : Level)
    → ----------------
    Set (l₀ ⊔ l₁ ⊔ (lsuc l₂))
  Famᴵ A l₂ = ∀ n → A n → Setᴵ l₂

  private
    l = l₀
  ----------------------------------------------------------------------
  -- Signatures (3.26)
  ----------------------------------------------------------------------
  record Sig : Set (lsuc l) where
    constructor mkSig
    field
      Op : Setᴵ l
      Ar : Famᴵ Op l

  open Sig public

  -- sum of signatures
  _⊕_ : Sig → Sig → Sig
  Op (X ⊕ Y) n        = Op X n + Op Y n
  Ar (X ⊕ Y) n (ι₁ a) = Ar X n a
  Ar (X ⊕ Y) n (ι₂ a) = Ar Y n a

  module SigFunctor
    {Σ : Sig}
    where
      ------------------------------------------------------------------
      -- Signature endofunctor (3.27)
      ------------------------------------------------------------------
      S : Setᴵ l → Setᴵ l
      S X n = ∑ a ∶ Op Σ n , (Ar Σ n a ⇁ X)

      -- functorial action
      S' :
        {X Y : Setᴵ l}
        (f : X ⇁ Y)
        → ----------
        S X ⇁ S Y
      S' f _ (a , b) = (a , f ∘ᴵ b)

      S'func :
        {X Y Z : Setᴵ l}
        {h : Y ⇁ Z}
        {g : X ⇁ Y}
        {n : I}
        (s : S X n)
        → ----------------------------------
        S' h n (S' g n s) == S' (h ∘ᴵ g) n s
      S'func _ = refl

      S'id :
        {X : Setᴵ l}
        (n : I)
        (s : S X n)
        → ----------
        s == S' idᴵ n s
      S'id _ _ = refl

      ------------------------------------------------------------------
      -- Algebra structure for a signature (3.28)
      ------------------------------------------------------------------
      record Alg (X : Setᴵ l) : Set l where
        constructor mkalg
        field sup : S X ⇁ X

      open Alg{{...}} public

      ------------------------------------------------------------------
      -- The property of being an S-algebra morphism (3.29)
      ------------------------------------------------------------------
      isHom :
        {X X' : Setᴵ l}
        {{_ : Alg X}}
        {{_ : Alg X'}}
        (h : X ⇁ X')
        → -------------
        Prop l
      isHom {{ξ}} {{ξ'}} h = ∀ n s → h n (sup n s) == sup n (S' h _ s)

      isHom∘ :
        {X X' X'' : Setᴵ l}
        {{_ : Alg X}}
        {{_ : Alg X'}}
        {{_ : Alg X''}}
        (h : X ⇁ X')
        (h' : X' ⇁ X'')
        → ---------------------------------
        isHom h → isHom h' → isHom (h' ∘ᴵ h)
      isHom∘ h h' ih ih' n s =
        proof
          h' n (h n (sup n s))
        =[ ap (h' n) (ih _ s) ]
          h' n (sup n (S' h n s))
        =[ ih' _ _ ]
          sup n (S' h' n (S' h n s))
        qed

      isHominv :
        {X X' : Setᴵ l}
        {{_ : Alg X}}
        {{_ : Alg X'}}
        (h : X ⇁ X')
        (_ : isHom h)
        {{β : ∀{n} → isIso (h n)}}
        → -----------------------------
        isHom λ n → (h n)⁻¹
      isHominv h ishomh n (a , b) =
        proof
          ((h n)⁻¹) (sup n (a , b))
        =[ ap (λ g → (h n ⁻¹) (sup n (a , g)))
           (funext (λ _ → funext (λ _ → symm (rinv _ _)))) ]
          ((h n)⁻¹) (sup n (a , λ m → h m ∘ (h m)⁻¹ ∘ b m))
        =[ ap (h n ⁻¹) (symm (ishomh _ _)) ]
          ((h n)⁻¹) (h n (sup n (a , λ m → (h m)⁻¹ ∘ b m)))
        =[ linv _ _ ]
          sup n (a , λ m → (h m)⁻¹ ∘ b m)
        qed

      ------------------------------------------------------------------
      -- Free Σ-algebra on an indexed set (3.30)
      ------------------------------------------------------------------
      data T (X : Setᴵ l) : Setᴵ l where
        η : X ⇁ T X
        σ : S (T X) ⇁ T X

      instance
        AlgT : {X : Setᴵ l} → Alg (T X)
        sup {{AlgT}} = σ

      -- existence part of universal property
      ⟦_⟧ :
        {X Y : Setᴵ l}
        {{_ : Alg Y}}
        {n : I}
        (t : T X n)
        (ρ : X ⇁ Y)
        → -----------------
        Y n
      ⟦ η _ x       ⟧ ρ = ρ _ x
      ⟦ σ _ (a , b) ⟧ ρ = sup _ (a , λ m x → ⟦ b m x ⟧ ρ)

      -- uniqueness part of universal property
      ⟦⟧uniq :
        {X Y : Setᴵ l}
        {{_ : Alg Y}}
        (ρ : X ⇁ Y)
        (h : T X ⇁ Y)
        (_ : isHom h)
        (_ : ∀ n x → h n (η n x) == ρ n x)
        (n : I)
        (t : T X n)
        → --------------------------------
        h n t == ⟦ t ⟧ ρ
      ⟦⟧uniq _ _ _     e n (η n x)       = e n x
      ⟦⟧uniq ρ h ishom e n (σ n (a , b)) =
        proof
          h n (σ n (a , b))
        =[ ishom n (a , b) ]
          sup n (a , h ∘ᴵ b)
        =[ ap
          (λ b' → sup n (a , b'))
          (funext λ m →
           funext λ x → ⟦⟧uniq ρ h ishom e m (b m x)) ]
          sup n (a , (λ m x → ⟦ b m x ⟧ ρ))
        qed

      -- functorial action
      T' :
        {X Y : Setᴵ l}
        (f : X ⇁ Y)
        → ------------
        T X  ⇁ T Y
      T' f _ t = ⟦ t ⟧ (η ∘ᴵ f)

      ⟦T⟧ :
        {X Y Z : Setᴵ l}
        {{_ : Alg Z}}
        (n : I)
        (t : T X n)
        {f : X ⇁ Y}
        {ρ : Y ⇁ Z}
        → ------------------------------
        ⟦ T' f n t ⟧ ρ == ⟦ t ⟧ (ρ ∘ᴵ f)
      ⟦T⟧ n t {f} {ρ} =
        ⟦⟧uniq
          (ρ ∘ᴵ f)
          (λ m t → ⟦ T' f m t ⟧ ρ)
          (λ _ _ → refl)
          (λ _ _ → refl)
          n
          t

      T'func :
        {X Y Z : Setᴵ l}
        {g : Y ⇁ Z}
        {f : X ⇁ Y}
        (n : I)
        (t : T X n)
        → ----------------------------------
        T' g n (T' f n t) == T' (g ∘ᴵ f) n t
      T'func n t = ⟦T⟧ n t

      T'id :
        {X : Setᴵ l}
        (n : I)
        (t : T X n)
        → -------------
        t == T' idᴵ n t
      T'id _ (η _ x)       = refl
      T'id _ (σ _ (a , b)) = ap (λ b' → σ _ (a , b'))
        (funext λ m → funext (λ x → T'id m (b m x)))

      ⟦⟧∘ :
        {X Y Z : Setᴵ l}
        ⦃ _ : Alg Y ⦄
        ⦃ _ : Alg Z ⦄
        (ρ : X ⇁ Y)
        (h : Y ⇁ Z)
        (_ : isHom h)
        (n : I)
        (t : T X n)
        → -----------------------------
        h n (⟦ t ⟧ ρ) == ⟦ t ⟧ (h ∘ᴵ ρ)
      ⟦⟧∘ ρ h ishom =
        ⟦⟧uniq
          (h ∘ᴵ ρ)
          (λ m t → h m (⟦ t ⟧ ρ))
          (λ{n (a , b) → ishom n (a , λ m x → ⟦ b m x ⟧ ρ)} )
          (λ _ _ → refl)

      -- insertion
      ι :
        {X : Setᴵ l}
        → -------------
        S X ⇁ T X
      ι n (a , b) = σ n (a , η ∘ᴵ b)

  open SigFunctor public

  ----------------------------------------------------------------------
  -- The WI-type generated by a signature in Setᴵ
  ----------------------------------------------------------------------
  𝕎 : (Σ : Sig) → Setᴵ l
  𝕎 Σ = T{Σ} (λ _ → 𝟘)

  ----------------------------------------------------------------------
  -- System of equations over a signature (3.31)
  ----------------------------------------------------------------------
  record Syseq (Σ : Sig) : Set (lsuc l) where
    constructor mkSyseq
    field
      Γ : Sig
    E = Op Γ
    V = Ar Γ
    field
      lhs : (n : I)(e : E n) → T{Σ} (V n e) n
      rhs : (n : I)(e : E n) → T{Σ} (V n e) n
  open Syseq

  -- satisfaction
  Sat :
    {Σ : Sig}
    {ε : Syseq Σ}
    (X : Setᴵ l)
    {{_ : Alg{Σ} X}}
    → ----------------
    Prop l
  Sat {ε = mkSyseq Γ l r} X =
    (n : I)(e : Op Γ n)(ρ : Ar Γ n e ⇁ X) → ⟦ l n e ⟧ ρ === ⟦ r n e ⟧ ρ

----------------------------------------------------------------------
-- Unindexed signatures
----------------------------------------------------------------------

{- Although unindexed version is the $I=𝟙$ case of the indexed
version, it is convenient to give it separately -}
module Unindexed
  {l : Level}
  where

  record Sig : Set (lsuc l) where
    constructor mkSig
    field
      Op : Set l
      Ar : Op → Set l
  open Sig public

  module SigFunctor
    {Σ : Sig}
    where

    S : Set l → Set l
    S X = ∑ a ∶ Op Σ , (Ar Σ a → X)

    record Alg (X : Set l) : Set l where
      constructor mkalg
      field sup : S X → X
    open Alg{{...}} public

    data T (X : Set l) : Set l where
      η : X → T X
      σ : S (T X) → T X

    instance
      AlgT : {X : Set l} → Alg (T X)
      sup {{AlgT}} = σ

  open SigFunctor public
  𝕎 : (Σ : Sig) → Set l
  𝕎 Σ = T{Σ} 𝟘

----------------------------------------------------------------------
-- Axioms for QWI-types (Definition 3.5)
----------------------------------------------------------------------
module _
  {l : Level}
  {I : Set l}
  (Σ : Slice.Sig I)
  (ε : Slice.Syseq _ Σ)
  where

  open Slice {l} I

  record QWItype : Set (lsuc l) where
    constructor mkQWItype
    field
      QWI : Setᴵ l
      {{AlgQWI}} : Alg {Σ} QWI
      -- QWI satisfies the equations
      satQWI : Sat {Σ} {ε} QWI
      -- and is intial among Sig-algebras satsifying the equations
      recQWI :
        {C : Setᴵ l}
        {{_  : Alg {Σ} C}}
        (_ : Sat {Σ} {ε} C)
        → ---------------
        QWI ⇁ C
      homrecQWI :
        {C : Setᴵ l}
        {{_  : Alg {Σ} C}}
        (satC : Sat {Σ} {ε} C)
        → --------------------
        isHom (recQWI satC)
      uniqQWI :
        {C : Setᴵ l}
        {{_  : Alg {Σ} C}}
        (satC : Sat {Σ} {ε} C)
        (h : QWI ⇁ C)
        (_ : isHom h)
        → --------------
        recQWI satC == h
