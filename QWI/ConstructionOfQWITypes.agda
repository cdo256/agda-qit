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
    IdxStructᵇ-ext :
      {i : Size}
      {A A' : IdxStructᵇ i}
      (_ : ∀ᵇ j < i , (domᵇ A j == domᵇ A' j))
      (_ : ∀ᵇ j < i , ∀ᵇ k < j , (
        (m : I)
        {t : T (domᵇ A k) m}
        {t' : T (domᵇ A' k) m}
        (_  : t === t')
        → ---------------------------
        τᵇ A j k m t === τᵇ A' j k m t')
      )
      → -------------------------------------
      A == A'
    IdxStructᵇ-ext e e' =
      match (funᵇ-ext e) λ{refl →
      match
        (funᵇ-ext λ j →
        funᵇ-ext λ k →
        funext λ m → heq-funext refl λ p → e' j k m p
        )
      λ{refl → refl}}

    --------------------------------------------------------------------
    -- Restricting elements of FixSizeStructᵇ to lower sizes
    --------------------------------------------------------------------
    FixSizeStructᵇ↓ᵇ :
      {i : Size}
      → --------------------------------------------
      FixSizeStructᵇ i → ∏ᵇ j < i , FixSizeStructᵇ j
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

        hyp : ∀ i → (∀ᵇ j < i , P j) → P i
        hyp i hi I@(D ∣ δ) I'@(D' ∣ δ')  =
          setext (IdxStructᵇ-ext domD=domD' ΤD=τD')
          where
          D↓ᵇ=D'↓ᵇ : ∀ᵇ j < i , (D ↓ᵇ j == D' ↓ᵇ j)
          D↓ᵇ=D'↓ᵇ j = ap el (hi j (FixSizeStructᵇ↓ᵇ I j) (FixSizeStructᵇ↓ᵇ I' j))

          domD=domD' : ∀ᵇ j < i , (domᵇ D j == domᵇ D' j)
          domD=domD' j =
            proof
              domᵇ D j
            =[ funext (∧e₁ (δ j)) ]
              ◇ (D ↓ᵇ j)
            =[ ap ◇ (D↓ᵇ=D'↓ᵇ j) ]
              ◇ (D' ↓ᵇ j)
            =[ symm (funext (∧e₁ (δ' j))) ]
              domᵇ D' j
            qed

          ΤD=τD' :  ∀ᵇ j < i , ∀ᵇ k < j , (
            (m : _)
            {t : T (SizeIdxStruct.Dᵇ D k) m}
            {t' : T (SizeIdxStruct.Dᵇ D' k) m}
            → --------------------------------------------------------------------
            t === t' → SizeIdxStruct.τᵇ D j k m t === SizeIdxStruct.τᵇ D' j k m t')
          ΤD=τD' j k m {t}{t'} t=t' =
            proof
              τᵇ D j k m t
            =[ ∧e₂ (δ j) k m t ]
              [ pairᵇ k t ]/ Rᵇ (D ↓ᵇ j) m
            =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ X m) (D↓ᵇ=D'↓ᵇ j) t=t' ]
              [ pairᵇ k t' ]/ Rᵇ (D' ↓ᵇ j) m
            =[ symm (∧e₂ (δ' j) k m t') ]
              τᵇ D' j k m t'
            qed

    --------------------------------------------------------------------
    -- Initial algebra structure up to size i exists
    --------------------------------------------------------------------
    initᵇ : ∀ i → FixSizeStructᵇ i
    initᵇ = <rec FixSizeStructᵇ hyp
      where
      hyp : ∀ i → (∏ᵇ j < i , FixSizeStructᵇ j) → FixSizeStructᵇ i
      hyp i hi = Di ∣ δ
        where
        domi : ∏ᵇ j < i , Setᴵ l
        domi j m = Wᵇ (el (hi j)) m / Rᵇ (el (hi j)) m

        domi< : ∀ᵇ j < i , ∀ᵇ k < j , ((m : I) → domi k m == domᵇ (el (hi j)) k m)
        domi< j k m =
          proof
            ◇ (el (hi k)) m
          =[ ap (λ f → (◇ ∘ el) f m) (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j) k)) ]
            ◇ (el (hi j) ↓ᵇ k) m
          =[ symm (∧e₁ (pf (hi j) k) m) ]
            domᵇ (el (hi j)) k m
          qed

        τi :  ∏ᵇ j < i , ∏ᵇ k < j , (T{Σ}(domi k) ⇁ domi j)
        τi j k m t =  [ pairᵇ k (T' (λ n → coe (domi< j k n)) m t) ]/ Rᵇ (el (hi j)) m

        τi< :
          ∀ᵇ j < i , ∀ᵇ k < j , ∀ᵇ l < k ,
          ((m : I)
          {t : T{Σ = Σ}(domi l) m}
          {t' : T (domᵇ (el (hi j)) l) m}
          (_ : t === t')
          → -------------------------------------
          τi k l m t === τᵇ (el (hi j)) k l m t')
        τi< j k l m {t} {t'} t=t' =
          proof
            [ pairᵇ l (T' (λ n → coe (domi< k l n)) m t) ]/ Rᵇ (el (hi k)) m
          =[ ap₂ (λ X x → [ pairᵇ l x ]/ Rᵇ (el X) m)
            (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j) k))
            (lemma e (funext λ n → domi< k l n) m t=t')
          ]
            [ pairᵇ l t' ]/ Rᵇ ((el (hi j)) ↓ᵇ k) m
          =[ symm (∧e₂ (pf (hi j) k) l m t') ]
            τᵇ (el (hi j)) k l m t'
          qed
          where
          e : domᵇ (el (FixSizeStructᵇ↓ᵇ (hi j) k)) l == domᵇ (el (hi k)) l
          e = ap (λ X → domᵇ (el X) l)
              (symm (FixSizeStructᵇ-uniq k (hi k) (FixSizeStructᵇ↓ᵇ (hi j) k)))

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

        Di↓ᵇ : ∀ᵇ j < i , (Di ↓ᵇ j == el (hi j))
        Di↓ᵇ j = IdxStructᵇ-ext
          (λ i → funext λ m → domi< j i m)
          (τi< j)

        domi↓ᵇ : ∀ᵇ j < i , (domi j == ◇ (Di ↓ᵇ j))
        domi↓ᵇ j = ap ◇ (symm (Di↓ᵇ j))

        δ : isFixSizeStructᵇ i Di
        δ j = ∧i
          (λ n → ap (λ f → f n) (domi↓ᵇ j))
          (λ k m t →
            (proof
              [ pairᵇ k (T' (λ n → coe (domi< j k n)) m t) ]/ Rᵇ (el (hi j)) m
            =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ X m)
              (symm (Di↓ᵇ j))
              (lemma (funext λ n → domi< j k n) m)
            ]
              [ pairᵇ k t ]/ Rᵇ (Di ↓ᵇ j) m
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

    FixSizeStructᵇ↓ᵇ-uniq : ∀ i → ∀ᵇ j < i ,
      (initᵇ j == FixSizeStructᵇ↓ᵇ (initᵇ i) j)
    FixSizeStructᵇ↓ᵇ-uniq i j =
      FixSizeStructᵇ-uniq j (initᵇ j) (FixSizeStructᵇ↓ᵇ (initᵇ i) j)

    ----------------------------------------------------------------------
    -- Construction of an element of FixSizeStruct
    ----------------------------------------------------------------------
    init : FixSizeStruct
    init = D ∣ δ
      where
      Q : Size → Setᴵ l
      Q i = ◇ (el (initᵇ i))

      Q< : ∀ i → ∀ᵇ j < i , (Q j == domᵇ (el (initᵇ i)) j)
      Q< i j =
        proof
          ◇ (el (initᵇ j))
        =[ ap (◇ ∘ el) (FixSizeStructᵇ↓ᵇ-uniq i j) ]
          ◇ (el (initᵇ i) ↓ᵇ j)
        =[ symm (funext λ n → ∧e₁ (pf (initᵇ i) j) n) ]
          domᵇ (el (initᵇ i)) j
        qed

      D : IdxStruct
      dom D        = Q
      τ  D i j m t =
        [ pairᵇ j (T' (λ n → coe (ap (λ f → f n)
          (Q< i j))) m t) ]/ Rᵇ(el (initᵇ i)) m

      D↓ : ∀ i → D ↓ i == el (initᵇ i)
      D↓ i = IdxStructᵇ-ext (Q< i) λ j k m {t}{t'} t=t' →
        proof
          [ pairᵇ k (T' (λ n → coe (ap (λ f → f n)
             (Q< j k))) m t) ]/ Rᵇ (el (initᵇ j)) m
        =[ ap₂ (λ X x → [ pairᵇ k x ]/ Rᵇ (el X) m)
          (FixSizeStructᵇ↓ᵇ-uniq i j)
          (lemma
            (ap (λ X → domᵇ (el X) k) (symm (FixSizeStructᵇ↓ᵇ-uniq i j)))
            (Q< j k) m t=t'
          )
        ]
          [ pairᵇ k t' ]/ Rᵇ (el (initᵇ i) ↓ᵇ j) m
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
        (λ j n t →
          proof
            [ pairᵇ j (T' (λ n → coe (ap (λ f → f n) (Q< i j))) n t) ]/ Rᵇ (el (initᵇ i)) n
          =[ ap₂ (λ X x → [ pairᵇ j x ]/ Rᵇ X n)
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
