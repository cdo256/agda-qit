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
    IdxStructᵇ-ext₀ :
      {i : Size}
      {Dᵇ  Dᵇ' : Dᵇ-type i}
      (dom-eq : ∀ᵇ i λ j {j<i} → Dᵇ j {j<i} == Dᵇ' j {j<i})
      {τᵇ  : τᵇ-type i Dᵇ}
      {τᵇ' : τᵇ-type i Dᵇ'}
      (τ-eq : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
              {t  : T (Dᵇ k {<ᵇ<ᵇ j<i k<j})} {t' : T (Dᵇ' k {<ᵇ<ᵇ j<i k<j})} →
              t === t' →
              τᵇ j {j<i} k {k<j} t  === τᵇ' j {j<i} k {k<j} t')
      → mkIdxStructᵇ Dᵇ τᵇ == mkIdxStructᵇ Dᵇ' τᵇ'
    IdxStructᵇ-ext₀ {i = i} {Dᵇ = Dᵇ} {Dᵇ' = Dᵇ'} dom-eq {τᵇ = τᵇ} {τᵇ' = τᵇ'} τ-eq =
      match (funᵇ-ext dom-eq) q
      where
      q : (p : Dᵇ === Dᵇ') →
           mkIdxStructᵇ Dᵇ τᵇ == mkIdxStructᵇ Dᵇ' τᵇ'
      q refl =
        let
          τ-eq' : τᵇ == τᵇ'
          τ-eq' =
            funᵇ-ext (λ j {j<i} →
            funᵇ-ext (λ k {k<j} →
            funext (λ t →
            τ-eq j {j<i} k {k<j} {t} {t} refl)))
        in match τ-eq' λ{refl → refl}
 
    IdxStructᵇ-ext :
      {i : Size}
      {A A' : IdxStructᵇ i}
      (dom-eq : ∀ᵇ i λ j {j<i} → (domᵇ A j {j<i} == domᵇ A' j {j<i}))
      (τ-eq : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
        {t : T (domᵇ A k)} {t' : T (domᵇ A' k)}
        (_  : t === t')
        → τᵇ A j {j<i} k {k<j} t === τᵇ A' j {j<i} k {k<j} t')
      → -------------------------------------
      A == A'
    IdxStructᵇ-ext
      {i = i}
      {A = A}
      {A' = A'}
      dom-eq τ-eq = IdxStructᵇ-ext₀ dom-eq τ-eq

    --------------------------------------------------------------------
    -- Restricting elements of FixSizeStructᵇ to lower sizes
    --------------------------------------------------------------------
    FixSizeStructᵇ↓ᵇ :
      {i : Size}
      → --------------------------------------------
      FixSizeStructᵇ i → ∏ᵇ i λ j {j<i} → FixSizeStructᵇ j
    FixSizeStructᵇ↓ᵇ (D ∣ δ) j {j<i} = _↓ᵇ_ D j {j<i} ∣ (λ k → δ k)

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
          D↓ᵇ=D'↓ᵇ : ∀ᵇ i λ j {j<i} → ((D ↓ᵇ j) {j<i} == (D' ↓ᵇ j) {j<i})
          D↓ᵇ=D'↓ᵇ j {j<i} =
            ap el (hi j {j<i} (FixSizeStructᵇ↓ᵇ I j {j<i})
                              (FixSizeStructᵇ↓ᵇ I' j {j<i}))

          domD=domD' : ∀ᵇ i λ j {j<i} → (domᵇ D j == domᵇ D' j)
          domD=domD' j {j<i} =
            proof
              domᵇ D j
            =[ ∧e₁ (δ j) ]
              ◇ ((D ↓ᵇ j) {j<i})
            =[ ap ◇ ((D↓ᵇ=D'↓ᵇ j) {j<i}) ]
              ◇ ((D' ↓ᵇ j) {j<i})
            =[ symm (∧e₁ (δ' j)) ]
              domᵇ D' j
            qed

          ΤD=τD' :  ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (∀ {t} {t'} →
            t === t' → τᵇ D j k t === τᵇ D' j k t')
          ΤD=τD' j {j<i} k {k<j} {t}{t'} t=t' =
            proof
              τᵇ D j k t
            =[ ∧e₂ (δ j) k t ]
              [ pairᵇ k t ]/ Rᵇ ((D ↓ᵇ j) {j<i})
            =[ ap₂ (λ X x → [ pairᵇ k {k<j} x ]/ Rᵇ X) (D↓ᵇ=D'↓ᵇ j {j<i}) t=t' ]
              [ pairᵇ k t' ]/ Rᵇ ((D' ↓ᵇ j) {j<i})
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
        domi j = Wᵇ (el (hi j {_})) / Rᵇ (el (hi j))

        domi< : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (domi k {<ᵇ<ᵇ j<i k<j} == domᵇ (el (hi j {j<i})) k)
        domi< j {j<i} k {k<j} =
          proof
            ◇ (el (hi k {<ᵇ<ᵇ j<i k<j}))
          =[ ap (◇ ∘ el) (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j {j<i}) k {k<j})) ]
            ◇ ((el (hi j {j<i}) ↓ᵇ k) {k<j})
          =[ symm (∧e₁ (pf (hi j) k)) ]
            domᵇ (el (hi j)) k
          qed

        τi :  ∏ᵇ i λ j {j<i} → ∏ᵇ j λ k {k<j} → (T{l}{Σ}(domi k {<ᵇ<ᵇ j<i k<j}) → domi j {j<i})
        τi j {j<i} k t =  [ pairᵇ k (T' {l} (coe (domi< j {j<i} k)) t) ]/ Rᵇ (el (hi j))

        τi< :
          ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → ∀ᵇ k λ l {l<k} →
          ({t : T{Σ = Σ}(domi l {<ᵇ<ᵇ j<i (<ᵇ<ᵇ k<j l<k)})}
          {t' : T (domᵇ (el (hi j {j<i})) l)}
          (_ : t === t')
          → -----------------------------------
          τi k {<ᵇ<ᵇ j<i k<j} l {l<k} t === τᵇ (el (hi j)) k l t')
        τi< j k {k<j} l {l<k} {t} {t'} t=t' =
          proof
            [ pairᵇ l {l<k} (T' (coe (domi< k l {l<k})) t) ]/ Rᵇ (el (hi k))
          =[ ap₂ (λ X x → [ pairᵇ l {l<k} x ]/ Rᵇ (el X))
            (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j {_}) k {k<j}))
            (lemma e (domi< k l {l<k}) t=t') ]
            [ pairᵇ l {l<k} t'  ]/ Rᵇ (((el (hi j {_})) ↓ᵇ k) {k<j})
          =[ symm (∧e₂ (pf (hi j {_}) k {_}) l t') ]
            τᵇ (el (hi j {_})) k {_} l t'
          qed
          where
          e : domᵇ (el (FixSizeStructᵇ↓ᵇ (hi j {_}) k {k<j})) l {l<k} == domᵇ (el (hi k {_})) l {l<k}
          e = ap (λ X → domᵇ (el X) l {l<k})
              (symm (FixSizeStructᵇ-uniq k (hi k {_}) (FixSizeStructᵇ↓ᵇ (hi j {_}) k {k<j})))

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

        Di↓ᵇ : ∀ᵇ i λ j {j<i} → ((Di ↓ᵇ j) {j<i} == el (hi j {j<i}))
        Di↓ᵇ j {j<i} = IdxStructᵇ-ext (domi< j {j<i}) (τi< j {j<i})

        domi↓ᵇ : ∀ᵇ i λ j {j<i} → (domi j {j<i}== ◇ ((Di ↓ᵇ j) {j<i}))
        domi↓ᵇ j {j<i} = ap ◇ (symm (Di↓ᵇ j {j<i}))

        δ : isFixSizeStructᵇ i Di
        δ j {j<i} = ∧i ((domi↓ᵇ j) {j<i}) λ k {k<j} t →
          proof
            [ pairᵇ k {_} (T' (coe (domi< j {j<i} k)) t) ]/ Rᵇ (el (hi j))
          =[ ap₂ (λ X x → [ pairᵇ k {k<j} x ]/ Rᵇ X) (symm (Di↓ᵇ j {j<i}))
            (lemma (domi< j {j<i} k)) ]
            [ pairᵇ k t ]/ Rᵇ ((Di ↓ᵇ j) {j<i})
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
      (initᵇ j == FixSizeStructᵇ↓ᵇ (initᵇ i) j {j<i})
    FixSizeStructᵇ↓ᵇ-uniq i j {j<i} =
      FixSizeStructᵇ-uniq j (initᵇ j) (FixSizeStructᵇ↓ᵇ (initᵇ i) j {j<i})

    ----------------------------------------------------------------------
    -- Construction of an element of FixSizeStruct
    ----------------------------------------------------------------------
    init : FixSizeStruct
    init = D ∣ δ
      where
      Q : Size → Set l
      Q i = ◇ (el (initᵇ i))

      Q< : ∀ i → ∀ᵇ i λ j {j<i} → (Q j == domᵇ (el (initᵇ i)) j)
      Q< i j {j<i} =
        proof
          ◇ (el (initᵇ j))
        =[ ap (◇ ∘ el) (FixSizeStructᵇ↓ᵇ-uniq i j {j<i}) ]
          ◇ ((el (initᵇ i) ↓ᵇ j) {j<i})
        =[ symm(∧e₁ (pf (initᵇ i) j {j<i})) ]
          domᵇ (el (initᵇ i)) j {j<i}
        qed

      D : IdxStruct
      dom D       = Q
      τ  D i j t = [ pairᵇ j ( T'(coe (Q< i j)) t) ]/ Rᵇ(el (initᵇ i))

      D↓ : ∀ i → D ↓ i == el (initᵇ i)
      D↓ i = IdxStructᵇ-ext (Q< i) λ j {j<i} k {k<j} {t} {t'} t=t' →
        proof
          [ pairᵇ k (T'(coe (Q< j k)) t) ]/ Rᵇ (el (initᵇ j))
        =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ (el X))
          (FixSizeStructᵇ↓ᵇ-uniq i j {j<i})
          (lemma (ap (λ X → domᵇ (el X) k {k<j})
            (symm (FixSizeStructᵇ↓ᵇ-uniq i j {j<i}))) (Q< j k) t=t') ]
          [ pairᵇ k t' ]/ Rᵇ ((el (initᵇ i) ↓ᵇ j) {j<i})
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
      δ i = ∧i (Q=Qᵇ↓ i) λ j {j<i} t →
        proof
          [ pairᵇ j (T' (coe (Q< i j)) t) ]/ Rᵇ (el (initᵇ i))
        =[ ap₂ (λ X x → [ pairᵇ j {j<i} x ]/ Rᵇ X)
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
