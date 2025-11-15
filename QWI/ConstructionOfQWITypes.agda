module QWI.ConstructionOfQWITypes where

open import QWI.FixedPointsAreQWITypes public

----------------------------------------------------------------------
-- Theorem 6.1: assuming IWISC, for every indexed signature Σ and
-- system of equations ε, there exists an initial algebra for Σ,ε
----------------------------------------------------------------------
module Main
  {l : Level}
  {I : Set l}
  (Σ : Slice.Sig I)
  (ε : Slice.Syseq I Σ)
  where
  open Slice I

  -- Theorem 6.1
  theorem : Inhabited (QWItype Σ ε)
  theorem with FxSzAlg→QWIType Σ ε
  ... | ∃i Size (∃i ssz (inhab fixSizeStruct→QWtype)) =
    inhab (fixSizeStruct→QWtype init)
    where
    instance
      _ : SizeStructure Size
      _ = ssz

    open SizeIdxStruct I Σ ε Size renaming (D to dom; Dᵇ to domᵇ)

    --------------------------------------------------------------------
    -- Extensionality principles for IdxStructᵇ
    --------------------------------------------------------------------
    IdxStructᵇ-ext₀ :
      {i : Size}
      {Dᵇ  Dᵇ' : Dᵇ-type i}
      (dom-eq : ∀ᵇ i λ j {j<i} → Dᵇ j {j<i} == Dᵇ' j {j<i})
      {τᵇ  : τᵇ-type i Dᵇ}
      {τᵇ' : τᵇ-type i Dᵇ'}
      (τ-eq : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (m : I) →
              {t : T (Dᵇ k {<ᵇ<ᵇ j<i k<j}) m}
              {t' : T (Dᵇ' k {<ᵇ<ᵇ j<i k<j}) m} →
              t === t' →
              τᵇ j {j<i} k {k<j} m t  === τᵇ' j {j<i} k {k<j} m t')
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
            funext (λ m →
            funext (λ t →
            τ-eq j {j<i} k {k<j} m {t} {t} refl))))
        in match τ-eq' λ{refl → refl}
 
    IdxStructᵇ-ext :
      {i : Size}
      {A A' : IdxStructᵇ i}
      (dom-eq : ∀ᵇ i λ j {j<i} → (domᵇ A j == domᵇ A' j))
      (τ-eq : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (
        (m : I)
        {t : T (domᵇ A k) m}
        {t' : T (domᵇ A' k) m}
        (_  : t === t')
        → ---------------------------
        τᵇ A j k {k<j} m t === τᵇ A' j k {k<j} m t')
      )
      → -------------------------------------
      A == A'
    IdxStructᵇ-ext dom-eq τ-eq = IdxStructᵇ-ext₀ dom-eq τ-eq

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
            =[ funext (∧e₁ (δ j)) ]
              ◇ ((D ↓ᵇ j) {j<i})
            =[ ap ◇ ((D↓ᵇ=D'↓ᵇ j) {j<i}) ]
              ◇ ((D' ↓ᵇ j) {j<i})
            =[ symm (funext (∧e₁ (δ' j))) ]
              domᵇ D' j
            qed

          ΤD=τD' : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (
            (m : _)
            {t : T (SizeIdxStruct.Dᵇ D k) m}
            {t' : T (SizeIdxStruct.Dᵇ D' k) m}
            → --------------------------------------------------------------------
            t === t' → SizeIdxStruct.τᵇ D j k m t === SizeIdxStruct.τᵇ D' j k m t')
          ΤD=τD' j {j<i} k {k<j} m {t}{t'} t=t' =
            proof
              τᵇ D j k m t
            =[ ∧e₂ (δ j) k m t ]
              [ pairᵇ k t ]/ Rᵇ ((D ↓ᵇ j) {j<i}) m
            =[ ap₂ (λ X x → [ pairᵇ k {k<j} x ]/ Rᵇ X m) (D↓ᵇ=D'↓ᵇ j {j<i}) t=t' ]
              [ pairᵇ k t' ]/ Rᵇ ((D' ↓ᵇ j) {j<i}) m
            =[ symm (∧e₂ (δ' j) k m t') ]
              τᵇ D' j k m t'
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
        domi : ∏ᵇ i λ j {j<i} → Setᴵ l
        domi j {j<i} m = Wᵇ (el (hi j {j<i})) m / Rᵇ (el (hi j {j<i})) m

        domi< : ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → ((m : I) → domi k {<ᵇ<ᵇ j<i k<j} m == domᵇ (el (hi j {j<i})) k m)
        domi< j {j<i} k {k<j} m =
          proof
            ◇ (el (hi k {<ᵇ<ᵇ j<i k<j})) m
          =[ ap (λ f → (◇ ∘ el) f m) (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j {j<i}) k {k<j})) ]
            ◇ ((el (hi j {j<i}) ↓ᵇ k) {k<j}) m
          =[ symm (∧e₁ (pf (hi j {j<i}) k {k<j}) m) ]
            domᵇ (el (hi j)) k m
          qed

        τi :  ∏ᵇ i λ j {j<i} → ∏ᵇ j λ k {k<j} → (T{Σ}(domi k {<ᵇ<ᵇ j<i k<j}) ⇁ domi j {j<i})
        τi j {j<i} k {k<j} m t =  [ pairᵇ k (T' (λ n → coe (domi< j k n)) m t) ]/ Rᵇ (el (hi j {j<i})) m

        τi< :
          ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → ∀ᵇ k λ l {l<k} →
          ((m : I)
          {t : T{Σ = Σ}(domi l) m}
          {t' : T (domᵇ (el (hi j {j<i})) l) m}
          (_ : t === t')
          → -------------------------------------
          τi k {<ᵇ<ᵇ j<i k<j} l {l<k} m t === τᵇ (el (hi j)) k l m t')
        τi< j {j<i} k {k<j} l {l<k} m {t} {t'} t=t' =
          proof
            [ pairᵇ l (T' (λ n → coe (domi< k l n)) m t) ]/ Rᵇ (el (hi k)) m
          =[ ap₂ (λ X x → [ pairᵇ l x ]/ Rᵇ (el X) m)
            (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j {j<i}) k {k<j}))
            (lemma e (funext λ n → domi< k l n) m t=t')
          ]
            [ pairᵇ l t' ]/ Rᵇ (((el (hi j {j<i})) ↓ᵇ k) {k<j}) m
          =[ symm (∧e₂ (pf (hi j) k) l m t') ]
            τᵇ (el (hi j)) k l m t'
          qed
          where
          e : domᵇ (el (FixSizeStructᵇ↓ᵇ (hi j {_}) k {k<j})) l {l<k} == domᵇ (el (hi k {_})) l {l<k}
          e = ap (λ X → domᵇ (el X) l {l<k})
              (symm (FixSizeStructᵇ-uniq k (hi k {_}) (FixSizeStructᵇ↓ᵇ (hi j {_}) k {k<j})))

          lemma :
            {X X' X'' : Setᴵ _}
            (_ : X' == X'')
            (e : X == X'')
            (m : I)
            {u : T{Σ = Σ} X m}
            {u' : T{Σ = Σ} X' m}
            (_ : u === u')
            → ------------------------------------------
            T' (λ n → coe (ap (λ f → f n) e)) m u === u'
          lemma {X} refl refl m {u} refl =
            proof
              T' (λ n → coe (ap (λ f → f n) {X} refl)) m u
            =[ ap (λ f → T' (λ n → f n) m u) (funext λ n → funext coerefl) ]
              T' idᴵ m u
            =[ symm (T'id m u) ]
              u
            qed

        Di : IdxStructᵇ i
        Di = mkIdxStructᵇ domi τi

        Di↓ᵇ : ∀ᵇ i λ j {j<i} → ((Di ↓ᵇ j) {j<i} == el (hi j {j<i}))
        Di↓ᵇ j {j<i} = IdxStructᵇ-ext
          (λ i {i<j} → funext λ m → domi< j i {i<j} m)
          (τi< j {j<i})

        domi↓ᵇ : ∀ᵇ i λ j {j<i} → (domi j {j<i}== ◇ ((Di ↓ᵇ j) {j<i}))
        domi↓ᵇ j {j<i} = ap ◇ (symm (Di↓ᵇ j {j<i}))

        δ : isFixSizeStructᵇ i Di
        δ j {j<i} = ∧i
          (λ n → ap (λ f → f n) (domi↓ᵇ j {j<i}))
          (λ k {k<j} m t →
            (proof
              [ pairᵇ k (T' (λ n → coe (domi< j k {k<j} n)) m t) ]/ Rᵇ (el (hi j)) m
            =[ ap₂ (λ X x → [ pairᵇ k {k<j} x ]/ Rᵇ X m)
              (symm (Di↓ᵇ j {j<i}))
              (lemma (funext λ n → domi< j k n) m)
            ]
              [ pairᵇ k t ]/ Rᵇ ((Di ↓ᵇ j) {j<i}) m
            qed)
          )
          where
          lemma :
            {X X' : Setᴵ _}
            (e : X == X')
            (m : I)
            {u : T{Σ = Σ} X m}
            → ----------------
            --T' (coe e) u === u
            T' (λ n → coe (ap (λ f → f n) e)) m u === u
          lemma {X} refl m {u} =
            proof
              --T' (coe refl) u
              T' (λ n → coe (ap (λ f → f n) {X} refl)) m u
            =[ ap (λ f → T' f m u) (funext λ n → funext coerefl) ]
              T' idᴵ m u
            =[ symm (T'id m u) ]
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
      Q : Size → Setᴵ l
      Q i = ◇ (el (initᵇ i))

      Q< : ∀ i → ∀ᵇ i λ j {j<i} → (Q j == domᵇ (el (initᵇ i)) j)
      Q< i j {j<i} =
        proof
          ◇ (el (initᵇ j))
        =[ ap (◇ ∘ el) (FixSizeStructᵇ↓ᵇ-uniq i j {j<i}) ]
          ◇ ((el (initᵇ i) ↓ᵇ j) {j<i})
        =[ symm (funext λ n → ∧e₁ (pf (initᵇ i) j) n) ]
          domᵇ (el (initᵇ i)) j
        qed

      D : IdxStruct
      dom D        = Q
      τ  D i j m t =
        [ pairᵇ j (T' (λ n → coe (ap (λ f → f n)
          (Q< i j))) m t) ]/ Rᵇ(el (initᵇ i)) m

      D↓ : ∀ i → D ↓ i == el (initᵇ i)
      D↓ i = IdxStructᵇ-ext (Q< i) λ j {j<i} k {k<j} m {t}{t'} t=t' →
        proof
          [ pairᵇ k (T' (λ n → coe (ap (λ f → f n)
             (Q< j k {k<j}))) m t) ]/ Rᵇ (el (initᵇ j)) m
        =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ (el X) m)
          (FixSizeStructᵇ↓ᵇ-uniq i j {j<i})
          (lemma
            (ap (λ X → domᵇ (el X) k {k<j}) (symm (FixSizeStructᵇ↓ᵇ-uniq i j {j<i})))
            (Q< j k {k<j}) m t=t'
          )
        ]
          [ pairᵇ k t' ]/ Rᵇ ((el (initᵇ i) ↓ᵇ j) {j<i}) m
        =[ symm (∧e₂ (pf (initᵇ i) j) k m t') ]
          τᵇ (el (initᵇ i)) j k m t'
        qed
        where
        lemma :
          {X X' X'' : Setᴵ _}
          (_ : X' == X'')
          (e : X == X'')
          (m : I)
          {u : T{Σ = Σ} X m}
          {u' : T{Σ = Σ} X' m}
          (_ : u === u')
          → ------------------------------------------
          T' (λ n → coe (ap (λ f → f n) e)) m u === u'
        lemma {X} refl refl m {u} refl =
          proof
            T' (λ n → coe (ap (λ f → f n) {X} refl)) m u
          =[ ap (λ f → T' f m u) (funext λ n → funext coerefl) ]
            T' idᴵ m u
          =[ symm (T'id m u) ]
            u
          qed

      δ : ◇fix D
      δ i = ∧i
        (λ n → ap (λ f → f n) (Q=Qᵇ↓ i))
        (λ j {j<i} n t →
          proof
            [ pairᵇ j (T' (λ n → coe (ap (λ f → f n) (Q< i j))) n t) ]/ Rᵇ (el (initᵇ i)) n
          =[ ap₂ (λ X x → [ pairᵇ j {j<i} x ]/ Rᵇ X n)
            (symm (D↓ i))
            (lemma (Q< i j) n)
          ]
            [ pairᵇ j t ]/ Rᵇ (D ↓ i) n
          qed
        )
        where
        Q=Qᵇ↓ : ∀ i → Q i == ◇ (D ↓ i)
        Q=Qᵇ↓ i = ap ◇ (symm (D↓ i))

        lemma :
          {X X' : Setᴵ _}
          (e : X == X')
          (m : I)
          {u : T{Σ = Σ} X m}
          → -----------------------------------------
          T' (λ n → coe (ap (λ f → f n) e)) m u === u
        lemma {X} refl m {u}  =
          proof
            T' (λ n → coe (ap (λ f → f n) {X} refl)) m u
          =[ ap (λ f → T' f m u) (funext λ n → funext coerefl) ]
            T' idᴵ m u
          =[ symm (T'id _ _) ]
            u
          qed
