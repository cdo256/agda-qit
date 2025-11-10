module QW.IndexedPolynomialFunctorsAndEquationalSystems where

open import TypeTheory public

----------------------------------------------------------------------
-- Signatures
----------------------------------------------------------------------
record Sig {l : Level} : Set (lsuc l) where
  constructor mkSig
  field
    Op : Set l
    Ar : Op → Set l

open Sig public

_⊕_ : {l : Level} → Sig {l} → Sig {l} → Sig {l}
X ⊕ Y = mkSig (Op X + Op Y) [ (Ar X) , (Ar Y) ]

module SigFunctor
  {l : Level}
  {Σ : Sig {l}}
  where
    ------------------------------------------------------------------
    -- Signature endofunctor
    ------------------------------------------------------------------
    S : Set l → Set l
    S X = ∑ a ∶ Op Σ , (Ar Σ a → X)

    -- functorial action
    S' :
      {X Y : Set l}
      (f : X → Y)
      → ----------
      S X → S Y
    S' f (a , b) = (a , f ∘ b)

    S'func :
      {X Y Z : Set l}
      {h : Y → Z}
      {g : X → Y}
      (s : S X)
      → ---------------------------
      S' h (S' g s) == S' (h ∘ g) s

    S'id :
      {X : Set l}
      (s : S X)
      → ----------
      s == S' id s
    S'id _ = refl
    S'func _ = refl

    ------------------------------------------------------------------
    -- Algebra structure for a signature
    ------------------------------------------------------------------
    record Alg (X : Set l) : Set l where
      constructor mkalg
      field sup : S X → X

    open Alg{{...}} public

    ------------------------------------------------------------------
    -- The property of being an S-algebra morphism
    ------------------------------------------------------------------
    isHom :
      {X X' : Set l}
      {{_ : Alg X}}
      {{_ : Alg X'}}
      (h : X → X')
      → ---------------
      Prop l
    isHom {{ξ}} {{ξ'}} h = ∀ s → h (sup {{ξ}} s) == sup {{ξ'}} (S' h s)

    isHom∘ :
      {X X' X'' : Set l}
      {{_ : Alg X}}
      {{_ : Alg X'}}
      {{_ : Alg X''}}
      (h : X → X')
      (h' : X' → X'')
      → ---------------------------------
      isHom h → isHom h' → isHom (h' ∘ h)
    isHom∘ h h' ih ih' s =
      proof
        h' (h (sup s))
      =[ ap h' (ih _) ]
        h' (sup (S' h s))
      =[ ih' _ ]
        sup (S' h' (S' h s))
      qed

    isHominv :
      {X X' : Set l}
      {{_ : Alg X}}
      {{_ : Alg X'}}
      (h : X → X')
      (_ : isHom h)
      {{β : isIso h}}
      → ---------------
      isHom (h ⁻¹)
    isHominv h ishomh s =
      proof
        (h ⁻¹) (sup s)
      =[ ap (λ f → (h ⁻¹) (sup (S' f s)))
         (quot.funext λ x → symm (rinv _ x)) ]
        (h ⁻¹) (sup (S' (h ∘ (h ⁻¹)) s))
      =[ refl ]
        (h ⁻¹) (sup (S' h (S' (h ⁻¹) s)))
      =[ ap (h ⁻¹) (symm (ishomh _)) ]
      (h ⁻¹) (h (sup (S' (h ⁻¹) s)))
      =[ linv _ _ ]
        sup (S' (h ⁻¹) s)
      qed

    ------------------------------------------------------------------
    -- Free Σ-algebra on a set
    ------------------------------------------------------------------
    data T (X : Set l) : Set l where
      η : X → T X
      σ : S (T X) → T X

    instance
      AlgT : {X : Set l} → Alg (T X)
      sup {{AlgT}} = σ

    -- existence part of universal property
    ⟦_⟧ :
      {X Y : Set l}
      {{_ : Alg Y}}
      (t : T X)
      (ρ : X → Y)
      → -----------------
      Y
    ⟦ η x       ⟧ ρ = ρ x
    ⟦ σ (a , b) ⟧ ρ = sup (a , λ x → ⟦ b x ⟧ ρ)

    -- uniqueness part of universal property
    ⟦⟧uniq :
      {X Y : Set l}
      {{_ : Alg Y}}
      (ρ : X → Y)
      (h : T X → Y)
      (_ : isHom h)
      (_ : ∀ x → h (η x) == ρ x)
      (t : T X)
      → ----------------------
      h t == ⟦ t ⟧ ρ
    ⟦⟧uniq _ _ _     e (η x)       = e x
    ⟦⟧uniq ρ h ishom e (σ (a , f)) =
      proof
        h (σ (a , f))
      =[ ishom (a , f) ]
        sup (a , h ∘ f)
      =[ ap (λ f' → sup (a , f'))
        (quot.funext (λ b → ⟦⟧uniq ρ h ishom e (f b))) ]
        sup (a , (λ b → ⟦ f b ⟧ ρ))
      qed

    -- functorial action
    T' :
      {X Y : Set l}
      (f : X → Y)
      → -------------
      T X → T Y
    T' f t = ⟦ t ⟧ (η ∘ f)

    ⟦T⟧ :
      {X Y Z : Set l}
      {{_ : Alg Z}}
      (t : T X)
      {f : X → Y}
      {ρ : Y → Z}
      → --------------------------
      ⟦ T' f t ⟧ ρ == ⟦ t ⟧ (ρ ∘ f)
    ⟦T⟧ t {f} {ρ} =
      ⟦⟧uniq
        (ρ ∘ f)
        (λ t → ⟦ T' f t ⟧ ρ)
        (λ _ → refl)
        (λ _ → refl)
        t

    T'func :
      {X Y Z : Set l}
      {g : Y → Z}
      {f : X → Y}
      (t : T X)
      → --------------------------
      T' g (T' f t) == T' (g ∘ f) t
    T'func t = ⟦T⟧ t

    T'id :
      {X : Set l}
      (t : T X)
      → ----------
      t == T' id t
    T'id (η x)       = refl
    T'id (σ (a , f)) = ap (λ f' → σ (a , f')) (quot.funext λ b → T'id (f b))

    ⟦⟧∘ :
      {X Y Z : Set l}
      ⦃ _ : Alg Y ⦄
      ⦃ _ : Alg Z ⦄
      (ρ : X → Y)
      (h : Y → Z)
      (_ : isHom h)
      (t : T X)
      → -------------------------
      h (⟦ t ⟧ ρ) == ⟦ t ⟧ (h ∘ ρ)
    ⟦⟧∘ ρ h ishom =
      ⟦⟧uniq
        (h ∘ ρ)
        (λ t → h (⟦ t ⟧ ρ))
        (λ{(a , f) → ishom (a , λ b → ⟦ f b ⟧ ρ)})
        (λ _ → refl)

    -- insertion
    ι :
      {X : Set l}
      → -------------
      S X → T X
    ι = σ ∘ S' η

open SigFunctor public

----------------------------------------------------------------------
-- The W-type generated by a signature
----------------------------------------------------------------------
𝕎 : {l : Level} (Σ : Sig {l}) → Set l
𝕎 {l} Σ = T{l}{Σ} 𝟘

----------------------------------------------------------------------
-- System of equations over a signature (Definition 3.1)
----------------------------------------------------------------------
Syseq : {l : Level} → Sig {l} → Set (lsuc l)
Syseq {l} Σ = ∑ Γ ∶ Sig ,
  ((e : Op Γ) → T{l}{Σ}(Ar Γ e)) × ((e : Op Γ) → T{l}{Σ}(Ar Γ e))

-- satisfaction
Sat :
  {l : Level}
  {Σ : Sig{l}}
  {ε : Syseq Σ}
  (X : Set l)
  {{_ : Alg{l}{Σ} X}}
  → ----------------
  Prop l
Sat {ε = (Γ , l , r)} X =
  (e : Op Γ)(ρ : Ar Γ e → X) → ⟦ l e ⟧ ρ === ⟦ r e ⟧ ρ

----------------------------------------------------------------------
-- Axioms for QW-types (Definition 3.2)
----------------------------------------------------------------------
module _
  {l : Level}
  (Σ : Sig {l})
  (Γ : Syseq Σ)
  where

  record QWtype : Set (lsuc l) where
    constructor mkQWtype
    field
      QW : Set l
      {{AlgQW}} : Alg {l} {Σ} QW
      -- QW satisfies the equations
      satQW : Sat {l} {Σ} {Γ} QW
      -- and is intial among Sig-algebras satsifying the equations
      recQW :
        {C : Set l}
        {{_  : Alg {l} {Σ} C}}
        (_ : Sat {l} {Σ} {Γ} C)
        → ---------------
        QW → C
      homrecQW :
        {C : Set l}
        {{_  : Alg {l} {Σ} C}}
        (satC : Sat {l} {Σ} {Γ} C)
        → ----------------
        isHom (recQW satC)
      uniqQW :
        {C : Set l}
        {{_  : Alg {l} {Σ} C}}
        (satC : Sat {l} {Σ} {Γ} C)
        (h : QW → C)
        (_ : isHom h)
        → ---------------
        recQW satC == h
