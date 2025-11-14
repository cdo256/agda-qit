module QW.ConstructionOfQWTypes where

open import QW.FixedPointsAreQWTypes public

----------------------------------------------------------------------
-- Theorem 6.1: assuming IWISC, for every signaturec Σ and system of
-- equations ε, there exists an initial algebra for Σ,ε
----------------------------------------------------------------------
module Main
  {l : Level}
  (Σ : Sig {l})
  (ε : Syseq Σ)
  where
  -- Theorem 6.1
  theorem : Inhabited (QWtype Σ ε)
  theorem with FxSzAlg→QWType Σ ε
  ... | ∃i Size (∃i ssz (inhab fixSizeStruct→QWtype)) =
    inhab (fixSizeStruct→QWtype init)
    where
    instance
      _ : SizeStructure Size
      _ = ssz

    open SizeIdxStruct Σ ε Size renaming (D to dom; Dᵇ to domᵇ)

    --------------------------------------------------------------------
    -- Extensionality principles for IdxStructᵇ
    --------------------------------------------------------------------
    IdxStructᵇ-ext :
      {i : Size}
      {A A' : IdxStructᵇ i}
      (_ : ∀ᵇ i λ j {j<i} → (domᵇ A j == domᵇ A' j))
      (_ : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
      ({t : T (domᵇ A k)}
        {t' : T (domᵇ A' k)}
        (_  : t === t')
        → ---------------------------
        τᵇ A j k t === τᵇ A' j k t'))
      → -------------------------------------
      A == A'
    IdxStructᵇ-ext e e' =
      match (funᵇ-ext e) λ{refl →
      match
        (funᵇ-ext λ j →
        funᵇ-ext λ k →
        heq-funext refl λ p → e' j k p)
      λ{refl → refl}}

    --------------------------------------------------------------------
    -- Restricting elements of FixSizeStructᵇ to lower sizes
    --------------------------------------------------------------------
    FixSizeStructᵇ↓ᵇ :
      {i : Size}
      → --------------------------------------------
      FixSizeStructᵇ i → ∏ᵇ i λ j {j<i} → FixSizeStructᵇ j
    FixSizeStructᵇ↓ᵇ (D ∣ δ) j = D ↓ᵇ j ∣ (λ k → δ k)

    --------------------------------------------------------------------
    -- Elements of FixSizeStructᵇ are unique if they exist
    --------------------------------------------------------------------
    FixSizeStructᵇ-uniq :
      (i : Size)
      (I I' : FixSizeStructᵇ i)
      → ---------------
      I == I'
    FixSizeStructᵇ-uniq = <ind P hyp
      where
        P : Size → Prop (lsuc l)
        P i = (I I' : FixSizeStructᵇ i) → I == I'

        hyp : ∀ i → (∀ᵇ i λ j {j<i} → P j) → P i
        hyp i hi I@(D ∣ δ) I'@(D' ∣ δ')  =
          setext (IdxStructᵇ-ext domD=domD' ΤD=τD')
          where
          D↓ᵇ=D'↓ᵇ : ∀ᵇ i λ j {j<i} → (D ↓ᵇ j == D' ↓ᵇ j)
          D↓ᵇ=D'↓ᵇ j = ap el (hi j (FixSizeStructᵇ↓ᵇ I j) (FixSizeStructᵇ↓ᵇ I' j))

          domD=domD' : ∀ᵇ i λ j {j<i} → (domᵇ D j == domᵇ D' j)
          domD=domD' j =
            proof
              domᵇ D j
            =[ ∧e₁ (δ j) ]
              ◇ (D ↓ᵇ j)
            =[ ap ◇ (D↓ᵇ=D'↓ᵇ j) ]
              ◇ (D' ↓ᵇ j)
            =[ symm (∧e₁ (δ' j)) ]
              domᵇ D' j
            qed

          ΤD=τD' :  ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (∀ {t} {t'} →
            t === t' → τᵇ D j k t === τᵇ D' j k t')
          ΤD=τD' j k {t}{t'} t=t' =
            proof
              τᵇ D j k t
            =[ ∧e₂ (δ j) k t ]
              [ pairᵇ k t ]/ Rᵇ (D ↓ᵇ j)
            =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ X) (D↓ᵇ=D'↓ᵇ j) t=t' ]
              [ pairᵇ k t' ]/ Rᵇ (D' ↓ᵇ j)
            =[ symm (∧e₂ (δ' j) k t') ]
              τᵇ D' j k t'
            qed

    --------------------------------------------------------------------
    -- Initial algebra structure up to size i exists
    --------------------------------------------------------------------
    initᵇ : ∀ i → FixSizeStructᵇ i
    initᵇ = <rec FixSizeStructᵇ hyp
      where
      hyp : ∀ i → (∏ᵇ i λ j {j<i} → FixSizeStructᵇ j) → FixSizeStructᵇ i
      hyp i hi = Di ∣ δ
        where
        domi : ∏ᵇ i λ j {j<i} → Set l
        domi j = Wᵇ (el (hi j)) / Rᵇ (el (hi j))

        domi< : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (domi k == domᵇ (el (hi j)) k)
        domi< j k =
          proof
            ◇ (el (hi k))
          =[ ap (◇ ∘ el) (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j) k)) ]
            ◇ (el (hi j) ↓ᵇ k)
          =[ symm (∧e₁ (pf (hi j) k)) ]
            domᵇ (el (hi j)) k
          qed

        τi :  ∏ᵇ i λ j {j<i} → ∏ᵇ j λ k {k<j} → (T{l}{Σ}(domi k) → domi j)
        τi j k t =  [ pairᵇ k (T' (coe (domi< j k)) t) ]/ Rᵇ (el (hi j))

        τi< :
          ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → ∀ᵇ k λ l {l<k} →
          ({t : T{Σ = Σ}(domi l)}
          {t' : T (domᵇ (el (hi j)) l)}
          (_ : t === t')
          → -----------------------------------
          τi k l t === τᵇ (el (hi j)) k l t')
        τi< j k l {t} {t'} t=t' =
          proof
            [ pairᵇ l (T' (coe (domi< k l)) t) ]/ Rᵇ (el (hi k))
          =[ ap₂ (λ X x → [ pairᵇ l x ]/ Rᵇ (el X))
            (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j) k))
            (lemma e (domi< k l) t=t') ]
            [ pairᵇ l t' ]/ Rᵇ ((el (hi j)) ↓ᵇ k)
          =[ symm (∧e₂ (pf (hi j) k) l t') ]
            τᵇ (el (hi j)) k l t'
          qed
          where
          e : domᵇ (el (FixSizeStructᵇ↓ᵇ (hi j) k)) l == domᵇ (el (hi k)) l
          e = ap (λ X → domᵇ (el X) l)
              (symm (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j) k)))

          lemma :
            {X X' X'' : Set _}
            (_ : X' == X'')
            (e : X == X'')
            {u : T{Σ = Σ} X}
            {u' : T{Σ = Σ} X'}
            (_ : u === u')
            → -----------------
            T' (coe e) u === u'
          lemma refl refl {u} refl =
            proof
              T' (coe refl) u
            =[ ap (λ f → T' f u) (funext coerefl) ]
              T' id u
            =[ symm (T'id _) ]
              u
            qed

        Di : IdxStructᵇ i
        Di = mkIdxStructᵇ domi τi

        Di↓ᵇ : ∀ᵇ i λ j {j<i} → (Di ↓ᵇ j == el (hi j))
        Di↓ᵇ j = IdxStructᵇ-ext (domi< j) (τi< j)

        domi↓ᵇ : ∀ᵇ i λ j {j<i} → (domi j == ◇ (Di ↓ᵇ j))
        domi↓ᵇ j = ap ◇ (symm (Di↓ᵇ j))

        δ : isFixSizeStructᵇ i Di
        δ j = ∧i (domi↓ᵇ j) λ k t →
          proof
            [ pairᵇ k (T' (coe (domi< j k)) t) ]/ Rᵇ (el (hi j))
          =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ X) (symm (Di↓ᵇ j))
            (lemma (domi< j k)) ]
            [ pairᵇ k t ]/ Rᵇ (Di ↓ᵇ j)
          qed
          where
          lemma :
            {X X' : Set _}
            (e : X == X')
            {u : T{Σ = Σ} X}
            → ----------------
            T' (coe e) u === u
          lemma refl {u}  =
            proof
              T' (coe refl) u
            =[ ap (λ f → T' f u) (funext coerefl) ]
              T' id u
            =[ symm (T'id _) ]
              u
            qed

    FixSizeStructᵇ↓ᵇ-uniq : ∀ i → ∀ᵇ i λ j {j<i} →
      (initᵇ j == FixSizeStructᵇ↓ᵇ (initᵇ i) j)
    FixSizeStructᵇ↓ᵇ-uniq i j =
      FixSizeStructᵇ-uniq j (initᵇ j) (FixSizeStructᵇ↓ᵇ (initᵇ i) j)

    ----------------------------------------------------------------------
    -- Construction of an element of FixSizeStruct
    ----------------------------------------------------------------------
    init : FixSizeStruct
    init = D ∣ δ
      where
      Q : Size → Set l
      Q i = ◇ (el (initᵇ i))

      Q< : ∀ i → ∀ᵇ i λ j {j<i} → (Q j == domᵇ (el (initᵇ i)) j)
      Q< i j =
        proof
          ◇ (el (initᵇ j))
        =[ ap (◇ ∘ el) (FixSizeStructᵇ↓ᵇ-uniq i j) ]
          ◇ (el (initᵇ i) ↓ᵇ j)
        =[ symm(∧e₁ (pf (initᵇ i) j)) ]
          domᵇ (el (initᵇ i)) j
        qed

      D : IdxStruct
      dom D       = Q
      τ  D i j t = [ pairᵇ j ( T'(coe (Q< i j)) t) ]/ Rᵇ(el (initᵇ i))

      D↓ : ∀ i → D ↓ i == el (initᵇ i)
      D↓ i = IdxStructᵇ-ext (Q< i) λ j k {t}{t'} t=t' →
        proof
          [ pairᵇ k (T'(coe (Q< j k)) t) ]/ Rᵇ (el (initᵇ j))
        =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ (el X))
          (FixSizeStructᵇ↓ᵇ-uniq i j)
          (lemma (ap (λ X → domᵇ (el X) k)
            (symm (FixSizeStructᵇ↓ᵇ-uniq i j))) (Q< j k) t=t') ]
          [ pairᵇ k t' ]/ Rᵇ (el (initᵇ i) ↓ᵇ j)
        =[ symm (∧e₂ (pf (initᵇ i) j) k t') ]
          τᵇ (el (initᵇ i)) j k t'
        qed
        where
        lemma :
          {X X' X'' : Set _}
          (_ : X' == X'')
          (e : X == X'')
          {u : T{Σ = Σ} X}
          {u' : T{Σ = Σ} X'}
          (_ : u === u')
          → -----------------
          T' (coe e) u === u'
        lemma refl refl {u} refl =
          proof
            T' (coe refl) u
          =[ ap (λ f → T' f u) (funext coerefl) ]
            T' id u
          =[ symm (T'id _) ]
            u
          qed

      δ : ◇fix D
      δ i = ∧i (Q=Qᵇ↓ i) λ j t →
        proof
          [ pairᵇ j (T' (coe (Q< i j)) t) ]/ Rᵇ (el (initᵇ i))
        =[ ap₂ (λ X x → [ pairᵇ j x ]/ Rᵇ X)
          (symm (D↓ i)) (lemma (Q< i j)) ]
          [ pairᵇ j t ]/ Rᵇ (D ↓ i)
        qed
        where
        Q=Qᵇ↓ : ∀ i → Q i == ◇ (D ↓ i)
        Q=Qᵇ↓ i = ap ◇ (symm (D↓ i))

        lemma :
          {X X' : Set _}
          (e : X == X')
          {u : T{Σ = Σ} X}
          → ----------------
          T' (coe e) u === u
        lemma refl {u}  =
          proof
            T' (coe refl) u
          =[ ap (λ f → T' f u) (funext coerefl) ]
            T' id u
          =[ symm (T'id _) ]
            u
          qed
