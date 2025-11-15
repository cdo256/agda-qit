module QWI.FixedPointsAreQWITypes where

open import QWI.SizeIndexedStructure public

----------------------------------------------------------------------
-- Proposition 6.4: given an indexed signature Σ (3.24) and system of
-- equations ε (3.29), there is a type of sizes Size,ssz such that any
-- ◇-fixed point gives an initial algebra for Σ,ε
----------------------------------------------------------------------
module _
  {l : Level}
  {I : Set l}
  (Σ : Slice.Sig I)
  (ε : Slice.Syseq I Σ)
  where
  open Slice I
  open Syseq ε
  private
    Ξ = Σ ⊕ Γ

    ∑OpΞ = ∑ I (Op Ξ)

    Arᴵ∑Ξ : ∑OpΞ → Setᴵ l
    Arᴵ∑Ξ = uncurry (Ar Ξ)

    Ar∑Ξ : ∑OpΞ → Set l
    Ar∑Ξ a = ∑ I (Arᴵ∑Ξ a)

  -- Proposition 6.4
  FxSzAlg→QWIType :
    ∃ Size ∶ Set l ,
    ∃ ssz ∶ SizeStructure Size ,
      (let open Colim Size {{ssz}} in
        Inhabited (SizeIdxStruct.FixSizeStruct I Σ ε Size {{ssz}} → QWItype Σ ε)
      )
  FxSzAlg→QWIType
    with IWISC (mkFam ∑OpΞ Ar∑Ξ)
  ... | ∃i (mkFam C F) w
    with IWISC (mkFam (∑ (c , a) ∶ C × (∑OpΞ) , (F c → Ar∑Ξ a)) λ{(_ , f) → ker f})
  ... | ∃i (mkFam C' F') w' =
    ∃i Size (∃i ssz
      (inhab getQWIType)
    )
    module _ where

    open CocontinuityOfTakingPowers.Inner I ∑OpΞ Arᴵ∑Ξ C F w C' F' w'
      using (Size ; ssz ; upperbounds ; isIsocan ; surjcan)
    instance
      _ : SizeStructure Size
      _ = ssz
      _ : UpperBounds _
      _ = upperbounds
    open SizeIdxStruct I Σ ε Size {{ssz}} renaming (D to ∣D_∣)
    open Colim Size

    getQWIType : FixSizeStruct → QWItype Σ ε
    getQWIType (A ∣ δ) =
      mkQWItype QWI {{AlgQWI}} satQWI recQWI homrecQWI uniqQWI
      where
      W : Size → Setᴵ l
      W i = Wᵇ (A ↓ i)

      R : ∀ i n → W i n → W i n → Prop l
      R i = Rᵇ (A ↓ i)

      Q : Size → Setᴵ l
      Q i n = W i n / R i n

      DA=Q : ∀{i} n → ∣D A ∣ i n == Q i n
      DA=Q {i} n = ∧e₁ (δ i) n

      τ=[pairᵇ]/R  : ∀{i} → ∀ᵇ i λ j {j<i} →
        (∀ n t → τ A i j {j<i} n t === [ pairᵇ j {j<i} t ]/ R i n)
      τ=[pairᵇ]/R {i} j {j<i} = ∧e₂ (δ i) j {j<i}

      W′ : ∀ i → ∏ᵇ i λ j {j<i} → (W j ⇁ W i)
      W′ i j {j<i} w (pairᵇ k {k<j} t) = pairᵇ k {<ᵇ<ᵇ j<i k<j} t

      Q′ : ∀ i → ∏ᵇ i λ j {j<i} → (Q j ⇁ Q i)
      Q′ i j {j<i} n = quot.lift
        {R = R j n}
        (λ z → [ W′ i j {j<i} n z ]/ R i n)
        λ
          { (τεᵇ k e ρ)   → quot.eq (R i n) (τεᵇ k e ρ)
          ; (τηᵇ k l t)   → quot.eq (R i n) (τηᵇ k l t)
          ; (τσᵇ k l a f) → quot.eq (R i n) (τσᵇ k l a f)
          }

      D′ : ∀ i → ∏ᵇ i λ j {j<i} → (∣D A ∣ j ⇁ ∣D A ∣ i)
      D′ i j {j<i} = τ A i j {j<i} ∘ᴵ η

      τ-surj :
        (i : Size)
        (n : I)
        (x : ∣D A ∣ i n)
        → ----------------------------------------------
        ∃ᵇ i λ j {j<i} → (∃ t ∶ T (∣D A ∣ j) n , τ A i j {j<i} n t == x)
      τ-surj i n x =
        match (quot.surjectionmk (R i n) (coe (DA=Q n) x))
        λ{(∃i (pairᵇ j {j<i} t) p) → ∃ᵇi j {j<i} (∃i t
          (proof
            τ A i j {j<i} n t
          =[ τ=[pairᵇ]/R j {j<i} n t ]
            [ pairᵇ j {j<i} t ]/ R i n
          =[ p ]
            coe (DA=Q n) x
          =[ coe=== (DA=Q n) x ]
            x
          qed))}

      D′=Q′ : ∀ i → ∀ᵇ i λ j {j<i} → (∀ n x →
        coe (DA=Q n) (D′ i j {j<i} n x) == Q′ i j {j<i} n (coe (DA=Q n) x))
      D′=Q′ i j {j<i} n x = match (τ-surj j n x) (λ {
        (∃ᵇi k {k<j} (∃i t refl)) →
          proof
            coe (DA=Q n) (τ A i j {j<i} n (η n (τ A j k {k<j} n t)))
          =[ coe===  (DA=Q n) _ ]
            τ A i j {j<i} n (η n (τ A j k {k<j} n t))
          =[ τ=[pairᵇ]/R {i = i} j {j<i} n _ ]
            [ pairᵇ j {j<i} (η n (τ A j k {k<j} n t)) ]/ R i n
          =[ quot.eq (R i n) (τηᵇ j {j<i} k {k<j} t) ]
            [ pairᵇ k {<ᵇ<ᵇ j<i k<j} t ]/ R i n
          =[ ap (Q′ i j {j<i} n)
            (symm (trans (τ=[pairᵇ]/R k {k<j} n t)
              (coe=== (DA=Q n) _))) ]
            Q′ i j {j<i} n (coe (DA=Q n) (τ A j k {k<j} n t))
          qed
        })

      Dact : ∀ i → ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (∀ n z →
        D′ i k n z == D′ i j n (D′ j k n z))
      Dact i j {j<i} k {k<j} n z =
        proof
          τ A i k {k<i} n (η n z)
        =[ τ=[pairᵇ]/R {i = i} k {j<i = k<i} n _ ]
          [ pairᵇ k {k<i} (η n z) ]/ R i n
        =[ symm (quot.eq (R i n) (τηᵇ j {j<i} k {k<j} (η n z))) ]
          [ pairᵇ j {j<i} (η n (τ A j k {k<j} n (η n z))) ]/ R i n
        =[ symm (τ=[pairᵇ]/R j {j<i} n _) ]
          τ A i j {j<i} n (η n (τ A j k {k<j} n (η n z)))
        qed
        where
          k<i : k <ᵇ i
          k<i = <ᵇ<ᵇ {i = k} {j = j} {k = i} j<i k<j

      τε : ∀ i → ∀ᵇ i λ j {j<i} →
        (
          (n : I)
          (e : Op Γ n)
          (ρ : Ar Γ n e ⇁ ∣D A ∣ j)
          → ----------------------------------------------------------
          τ A i j n (T' ρ n (lhs n e)) == τ A i j n (T' ρ n (rhs n e))
        )
      τε i j {j<i} n e ρ =
        proof
          τ A i j {j<i} n (T' ρ n (lhs n e))
        =[ τ=[pairᵇ]/R j {j<i} n _ ]
          [ pairᵇ j {j<i} (T' ρ n (lhs n e)) ]/ R i n
        =[ quot.eq (R i n) (τεᵇ j {j<i} e ρ) ]
          [ pairᵇ j {j<i} (T' ρ n (rhs n e)) ]/ R i n
        =[ symm (τ=[pairᵇ]/R j {j<i} n _) ]
          τ A i j {j<i} n (T' ρ n (rhs n e))
        qed

      τη : ∀ i → ∀ᵇ i λ j {j<i} →
        (
          (n : I)
          (z : ∣D A ∣ j n)
          → -----------------------------
          τ A i j {j<i} n (η n z) == D′ i j {j<i} n z
        )
      τη _ _ _ _ = refl

      τσ : ∀ i → ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} →
        (
          (m : I)
          (a : Op Σ m)
          (f : Ar Σ m a ⇁ T (∣D A ∣ k))
          → ---------------------------------------------------
          τ A i k {<ᵇ<ᵇ j<i k<j} m (σ m (a , f)) ==
          τ A i j {j<i} m (σ m (a , λ n b → η n (τ A j k {k<j} n (f n b))))
        )
      τσ i j {j<i} k {k<j} m a f =
        proof
          τ A i k {k<i} m (σ m (a , f))
        =[ τ=[pairᵇ]/R {i = i} k {j<i = k<i} m _ ]
          [ pairᵇ k {k<i} (σ m (a , f)) ]/ R i m
        =[ quot.eq (R i m) (τσᵇ j {j<i} k {k<j} a f) ]
          [ pairᵇ j {j<i} (σ m (a , λ n b → η n (τ A j k {k<j} n (f n b)))) ]/ R i m
        =[ symm (τ=[pairᵇ]/R j {j<i} m _) ]
          τ A i j {j<i} m (σ m (a , λ n b → η n (τ A j k {k<j} n (f n b))))
        qed
        where
          k<i : k <ᵇ i
          k<i = <ᵇ<ᵇ {i = k} {j = j} {k = i} j<i k<j

      D′τ :  ∀ i → ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (∀ n t →
        D′ i j {j<i} n (τ A j k {k<j} n t) == τ A i k {<ᵇ<ᵇ j<i k<j} n t)
      D′τ i j {j<i} k {k<j} n t =
        proof
          τ A i j {j<i} n (η n (τ A j k {k<j} n t))
        =[ τ=[pairᵇ]/R j {j<i} n _ ]
          [ pairᵇ j {j<i} (η n (τ A j k {k<j} n t)) ]/ R i n
        =[ quot.eq (R i n) (τηᵇ j {j<i} k {k<j} t) ]
          [ pairᵇ k {k<i} t ]/ R i n
        =[ symm (τ=[pairᵇ]/R {i = i} k {j<i = k<i} n _) ]
          τ A i k {k<i} n t
        qed
        where
          k<i : k <ᵇ i
          k<i = <ᵇ<ᵇ {i = k} {j = j} {k = i} j<i k<j

      τD′ :
        (i  j : Size)
        {j<i : j <ᵇ i}
        (m : I)
        (t : T (∣D A ∣ j) m)
        → --------------------------------
        set k ∶ Size , (⋀ i<k ∶ i <ᵇ k ,
          τ A k j {<ᵇ<ᵇ i<k j<i} m t ==
          τ A k i {i<k} m (T' (D′ i j {j<i}) m t))
      τD′ i j {j<i} m (η m x) =
        let
          k : Size
          k = ↑ˢ i
          i<k : i <ᵇ k
          i<k = <ᵇ↑ˢ
          j<k : j <ᵇ k
          j<k = <ᵇ<ᵇ i<k j<i
        in k ∣ ⋀i i<k
        (proof
          τ A k j {j<k} m (η m x)
        =[ τη k j {j<k} m _ ]
          D′ k j {j<k} m x
        =[ Dact k i {i<k} j {j<i} m x ]
          D′ k i {i<k} m (D′ i j {j<i} m x)
        =[ symm (τη k i {i<k} m _) ]
          τ A k i {i<k} m (η m (D′ i j {j<i} m x))
        qed)
      τD′ i j {j<i} m (σ _ (a , f)) =
        let
          g : ∑ I (Ar Σ m a) → Size
          g = λ{(n , b) → el (τD′ i j {j<i} n (f n b))}

          i<ᵇg : ∀ n b → i <ᵇ g (n , b)
          i<ᵇg n b = ⋀e₁ (pf (τD′ i j n (f n b)))

          j<ᵇg : ∀ n b → j <ᵇ g (n , b)
          j<ᵇg n b = <ᵇ<ᵇ (i<ᵇg n b) j<i

          e :
            (n : I)
            (b : Ar Σ m a n)
            → -------------------------------------------------
            τ A (g(n , b)) j {j<ᵇg n b} n (f n b) ==
            τ A (g(n , b)) i {i<ᵇg n b} n (T' (D′ i j {j<i}) n (f n b))
          e n b = ⋀e₂ (pf (τD′ i j n (f n b)))

          k : Size
          k = i ∨ˢ  ⋁ˢ (m , ι₁ a) g

          g<ᵇk : ∀ n b → g(n , b) <ᵇ k
          g<ᵇk n b = <ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ⋁ˢ g (n , b))

          l : Size
          l = ↑ˢ k

          instance
            i<k : i <ᵇ k
            i<k = <ᵇ∨ˢl _
            k<l : k <ᵇ l
            k<l = <ᵇ↑ˢ
            i<l : i <ᵇ l
            i<l = <ᵇ<ᵇ k<l i<k
        in l ∣ (⋀i i<l
          (proof
            τ A l j m (σ m (a , f))
          =[  τσ l k {k<l} j {<ᵇ<ᵇ i<k j<i} _ _ _  ]
            τ A l k {k<l} m (σ m (a , λ n b → η n (τ A k j {<ᵇ<ᵇ i<k j<i} n (f n b))))
          =[ ap (λ f' → τ A l k {k<l} m (σ m (a , f'))) (funext λ n → funext λ b →
              ap (η n) (symm (D′τ k (g (n , b)) {g<ᵇk n b} j {j<ᵇg n b} n (f n b)))) ]
            τ A l k {k<l} m (σ m (a , λ n b → η n (D′ k (g (n , b)) {g<ᵇk n b} n
              (τ A (g (n , b)) j {j<ᵇg n b} n (f n b)))))
          =[ ap (λ h → τ A l k {k<l} m (σ m (a , h))) (funext λ n → funext λ b →
              ap (η {Σ} n ∘ D′ k (g (n , b)) {g<ᵇk n b} n) (e n b) ) ]
              τ A l k {k<l} m (σ m (a , λ n b → η n (D′ k (g (n , b)) {g<ᵇk n b} n
              (τ A (g (n , b)) i {i<ᵇg n b} n (T' (D′ i j {j<i}) n (f n b))))))
          =[ ap (λ h → τ A l k {k<l} m (σ m (a , h))) (funext λ n → funext λ b →
              ap (η {Σ} n) (D′τ k (g (n , b)) {g<ᵇk n b} i {i<ᵇg n b} n
                (T' (D′ i j {j<i}) n (f n b)) )) ]
              τ A l k {k<l} m (σ m (a , λ n b → η n (τ A k i {i<k} n (T' (D′ i j {j<i}) n (f n b)))))
          =[ symm (τσ l k {k<l} i {i<k} _ _ _) ]
            τ A l i {i<l} m (σ m (a , λ n b → T' (D′ i j {j<i}) n (f n b)))
        qed))

      -- Definition of the inital algebra for (Σ, ε) as a colimit
      D : I → Diag
      vtx (D n) i     = ∣D A ∣ i n
      edg (D n) i j {j<i}   = D′ i j {j<i} n
      act (D n) i j {j<i} k {k<j} = Dact i j {j<i} k {k<j} n

      QWI : Setᴵ l
      QWI n = colim (D n)

      -- QWI is a Σ-algebra
      instance
        canSΣDiso : ∀ {n} → isIso (canS {I} {Σ} D n)
        canSΣDiso {n} =
          CocontinuityOfPolynomialEndofunctors.Scont
            Σ ε Size ssz isIsocan D n
        AlgQWI : Alg {Σ} QWI
        sup {{AlgQWI}} m = (∫ (S∘ {I} {Σ} D m) φ Coconeφ) ∘ (canS {I} {Σ} D m)⁻¹
          module _ where
          φ : (i : Size) → S{Σ}(∣D A ∣ i) m → QWI m
          φ i s = ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (ι m s))

          Coconeφ : Cocone (S∘ {I} {Σ} D m) φ
          Coconeφ i j {j<i} s =
            let
              k : Size
              k = el (τD′ i j {j<i} m (ι m s))
              k' : Size
              k' = ↑ˢ i ∨ˢ ↑ˢ j ∨ˢ k
              instance
                i<ᵇk : i <ᵇ k
                i<ᵇk = ⋀e₁ (pf (τD′ i j {j<i} m (ι m s)))

                j<ᵇk : j <ᵇ k
                j<ᵇk = <ᵇ<ᵇ i<ᵇk j<i

                ↑ˢj<ᵇk' : ↑ˢ j <ᵇ k'
                ↑ˢj<ᵇk' = <ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ∨ˢl _)

                i<ᵇk' : i <ᵇ k'
                i<ᵇk' = <ᵇ<ᵇ (<ᵇ∨ˢl _) <ᵇ↑ˢ

                j<ᵇk' : j <ᵇ k'
                j<ᵇk' = <ᵇ<ᵇ (↑ˢj<ᵇk') <ᵇ↑ˢ

                k<ᵇk' : k <ᵇ k'
                k<ᵇk' = <ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ∨ˢr _)

                ↑ˢi<ᵇk' : ↑ˢ i <ᵇ k'
                ↑ˢi<ᵇk' = <ᵇ∨ˢl _

                e : τ A k j {j<ᵇk} m (ι m s) == τ A k i {i<ᵇk} m (T' (D′ i j {j<i}) m (ι m s))
                e = ⋀e₂ (pf (τD′ i j {j<i} m (ι m s)))
              in
                proof
                  ν (D m) (↑ˢ j) (τ A (↑ˢ j) j {<ᵇ↑ˢ} m (ι m s))
                =[ Coconeν (D m) k' (↑ˢ j) _ ]
                  ν (D m) k' (D′ k' (↑ˢ j) m (τ A (↑ˢ j) j {<ᵇ↑ˢ} m (ι m s)))
                =[ ap (ν (D m) k') (D′τ k' (↑ˢ j) {↑ˢj<ᵇk'} j {<ᵇ↑ˢ} m _) ]
                  ν (D m) k' (τ A k' j {j<ᵇk'} m (ι m s))
                =[ ap (ν (D m) k') (symm (D′τ k' k {k<ᵇk'} j {j<ᵇk} m _)) ]
                  ν (D m) k' (D′ k' k {k<ᵇk'} m (τ A k j {j<ᵇk} m (ι m s)))
                =[ ap (ν (D m) k' ∘ D′ k' k {k<ᵇk'} m) e ]
                  ν (D m) k' (D′ k' k {k<ᵇk'} m (τ A k i {i<ᵇk} m (T' (D′ i j {j<i}) m (ι m s))))
                =[ ap (ν (D m) k') (D′τ k' k {k<ᵇk'} i {i<ᵇk} m _) ]
                  ν (D m) k' (τ A k' i {i<ᵇk'} m (T' (D′ i j {j<i}) m (ι m s)))
                =[ ap (ν (D m) k') (symm (D′τ k' (↑ˢ i) {↑ˢi<ᵇk'} i {<ᵇ↑ˢ} m _)) ]
                  ν (D m) k' (D′ k' (↑ˢ i) {↑ˢi<ᵇk'} m
                  (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (T' (D′ i j {j<i}) m (ι m s))))
                =[ symm (Coconeν (D m) k' (↑ˢ i) {↑ˢi<ᵇk'} _ ) ]
                  ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (T' (D′ i j {j<i}) m (ι m s)))
                qed

      -- QWI satisfies the equational system
      ⟦⟧ν :
        ∀ i → ∀ᵇ i λ j {j<i} →
          ((m : I)
          (t : T{Σ} (∣D A ∣ j) m)
          → --------------------------------
          ⟦ t ⟧ (λ n → ν (D n) j) == ν (D m) i (τ A i j {j<i} m t))
      ⟦⟧ν i j {j<i} m (η .m x) =
        proof
          ν (D m) j x
        =[ Coconeν (D m) i j {j<i} x ]
          ν (D m) i (D′ i j {j<i} m x)
        =[ ap (ν (D m) i) (symm (τη _ _ _ _)) ]
          ν (D m) i (τ A i j {j<i} m (η m x))
        qed
      ⟦⟧ν i j {j<i} m (σ .m (a , f)) =
        proof
          ∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m)
            (((canS {I} {Σ} D m)⁻¹)
              (a , λ n b → ⟦ f n b ⟧ λ n → ν (D n) j))
        =[ ap (λ g → ∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m)
              (((canS {I} {Σ} D m)⁻¹) (a , g)))
            (funext λ n → funext λ b → ⟦⟧ν i j n (f n b)) ]
          ∫ (S∘ {I} {Σ} D m) {QWI m} (φ m) (Coconeφ m)
            (((canS {I} {Σ} D m)⁻¹)
              (S' {Σ} (λ n → ν (D n) i) m
                (a , λ n b → τ A i j {j<i} n (f n b))))
        =[ ap (∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m)) canS⁻¹Sν ]
          ∫ (S∘ {I} {Σ} D m) {QWI m} (φ m) (Coconeφ m)
            (ν (S∘ {I} {Σ} D m) i ((a , λ n b → τ A i j {j<i} n (f n b))))
        =[ refl ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (T' (τ A i j {j<i}) m (σ m (a , η ∘ᴵ f))))
        =[ ap (ν (D m) (↑ˢ i)) (symm (τσ (↑ˢ i) i {<ᵇ↑ˢ} j {j<i} _ _ _)) ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) j {<ᵇ<ᵇ <ᵇ↑ˢ j<i} m (σ m (a , f)))
        =[ ap (ν (D m) (↑ˢ i)) (symm (D′τ (↑ˢ i) i {<ᵇ↑ˢ} j {j<i} m _)) ]
          ν (D m) (↑ˢ i) (D′ (↑ˢ i) i {<ᵇ↑ˢ} m (τ A i j {j<i} m (σ m (a , f))))
        =[ symm (Coconeν (D m) (↑ˢ i) i {<ᵇ↑ˢ} _) ]
          ν (D m) i (τ A i j {j<i} m (σ m (a , f)))
        qed
        where
        open CocontinuityOfPolynomialEndofunctors Ξ
        canS⁻¹Sν :
            ((canS {I} {Σ} D m)⁻¹)
              (S' {Σ} (λ n → ν (D n) i) m (a , λ n b → τ A i j {j<i} n (f n b)))
          ===
            ν (S∘ {I} {Σ} D m) i ((a , λ n b → τ A i j {j<i} n (f n b)))
        canS⁻¹Sν = linv (canS {I} {Σ} D m) _

      satQWI : Sat {Σ} {ε} QWI
      satQWI m e ρ = match (surjcan (m , ι₂ e) D ρ)
        λ { (∃i i (∃i ρi refl)) →
        proof
          ⟦ lhs m e ⟧ (λ n → ν (D n) i ∘ ρi n)
        =[ symm (⟦T⟧ m (lhs m e))  ]
          ⟦ T' ρi m (lhs m e) ⟧ (λ n → ν (D n) i)
        =[ ⟦⟧ν  (↑ˢ i) i {<ᵇ↑ˢ} _ _ ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (T' ρi m (lhs m e)))
        =[ ap (ν (D m) (↑ˢ i)) (τε (↑ˢ i) i {<ᵇ↑ˢ} _ _ _) ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (T' ρi m (rhs m e)))
        =[ symm (⟦⟧ν (↑ˢ i) i {<ᵇ↑ˢ} _ _) ]
          ⟦ T' ρi m (rhs m e) ⟧ (λ n → ν (D n) i)
        =[ ⟦T⟧ m (rhs m e) ]
          ⟦ rhs m e ⟧ (λ n → ν (D n) i ∘ ρi n)
        qed}

      -- Universal property of QWI
      module _
        {C   : Setᴵ l}
        {{AlgC  : Alg C}}
        (satC : Sat {Σ} {ε} C)
        where
        rec : ∀ i → ∣D A ∣ i ⇁ C
        rec = λ i m → fun (rec' i) m ∘ coe (DA=Q m)
          module _ where
          record Fun (i : Size) : Set l where
            field
              fun  : ∀ m → W i m / R i m → C m
              funτ : ∀ m → ∀ᵇ i λ j {j<i} →
                ((t : T (∣D A ∣ j) m)
                → ---------------------------------
                fun m ([ pairᵇ j {j<i} t ]/ R i m) ==
                ⟦ t ⟧ (λ n → (fun n ∘ coe (DA=Q n) ∘ D′ i j {j<i} n)))
          open Fun public

          fun∘Q′ :
            (i : Size)
            (hi : ∏ᵇ i λ j {j<i} → Fun j)
            (k j : Size)
            {j<i : j <ᵇ i}
            {k<j : k <ᵇ j}
            → -------------------------------------------
            ∀ m → fun (hi k {<ᵇ<ᵇ j<i k<j}) m == fun (hi j {j<i}) m ∘ Q′ j k {k<j} m
          fun∘Q′ i hi = wf.ind _<_ <iswf P
            λ k hk → hyp k (λ l {l<ᵇk} → hk l l<ᵇk)
            where
            P : Size → Prop l
            P k =
              (j : Size)
              {j<i : j <ᵇ i}
              {k<j : k <ᵇ j}
              → -------------------------------------------
              ∀ m → fun (hi k) m == fun (hi j) m ∘ Q′ j k {k<j} m

            hyp : ∀ k → (∀ᵇ k λ l {l<k} → P l) → P k
            hyp k hk j {j<i} {k<j} m = funext (quot.ind (R k m)
              (λ z → fun (hi k) m z == fun (hi j) m (Q′ j k {k<j} m z))
              (λ{(pairᵇ l {l<k} t) →
                proof
                  fun (hi k) m ([ pairᵇ l {l<k} t ]/ R k m)
                =[ funτ (hi k) m l t ]
                  ⟦ t ⟧ (λ n → fun (hi k) n ∘ coe (DA=Q n) ∘ D′ k l {l<k} n)
                =[ ap (λ f → ⟦ t ⟧ (λ n → fun (hi k {<ᵇ<ᵇ j<i k<j}) n ∘ f n))
                  (funext (λ n → funext (D′=Q′ k l {l<k} n)))
                ]
                  ⟦ t ⟧ (λ n → fun (hi k) n ∘ Q′ k l {l<k} n ∘ coe (DA=Q n))
                =[ ap (λ f → ⟦ t ⟧ (λ n → f n ∘ coe (DA=Q n)))
                  (symm (funext (hk l {l<k} k {<ᵇ<ᵇ j<i k<j} {l<k})))
                ]
                  ⟦ t ⟧ (λ n → fun (hi l) n ∘ coe (DA=Q n))
                =[ ap (λ f → ⟦ t ⟧ (λ n → f n ∘ coe (DA=Q n)))
                  (funext (hk l {l<k} j {j<i} {<ᵇ<ᵇ k<j l<k}))
                ]
                  ⟦ t ⟧ (λ n → fun (hi j) n ∘ Q′ j l {<ᵇ<ᵇ k<j l<k} n ∘ coe (DA=Q n))
                =[ ap (λ f → ⟦ t ⟧ (λ n → fun (hi j {j<i}) n ∘ f n))
                  (symm (funext (λ n → funext ((D′=Q′ j l {<ᵇ<ᵇ k<j l<k} n)))))
                ]
                  ⟦ t ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ D′ j l {<ᵇ<ᵇ k<j l<k} n)
                =[ symm (funτ (hi j) m l t) ]
                  fun (hi j) m ([ pairᵇ l {<ᵇ<ᵇ k<j l<k} t ]/ R j m)
                qed}))

          rec' : ∀ i → Fun i
          rec' = <rec Fun hyp
            where
            hyp : ∀ i → (∏ᵇ i λ j {j<i} → Fun j) → Fun i
            hyp i hi = record { fun = funhyp ; funτ = funτhyp }
              where
              funhyp : ∀ m → W i m / R i m → C m
              funhyp m = quot.lift {R = R i m}
                (λ{(pairᵇ j {j<i} t) → ⟦ t ⟧ (λ n → fun (hi j {j<i}) n ∘ coe (DA=Q n))})
                (λ{(τεᵇ j {j<i} e ρ) →
                  proof
                    ⟦ T' ρ m (lhs m e) ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n))
                  =[ ⟦T⟧ m (lhs m e) ]
                    ⟦ lhs m e ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ ρ n)
                  =[ satC m e (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ ρ n) ]
                    ⟦ rhs m e ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ ρ n)
                  =[ symm ( ⟦T⟧ m (rhs m e)) ]
                    ⟦ T' ρ m (rhs m e) ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n))
                  qed
                ;(τηᵇ j {j<i} k {k<j} t) →
                  proof
                    fun (hi j) m (coe (DA=Q m) (τ A j k {k<j} m t))
                  =[ ap (fun (hi j) m)
                      (trans (τ=[pairᵇ]/R k {k<j} m t) (coe=== (DA=Q m) _)) ]
                    fun (hi j) m ([ pairᵇ k {k<j} t ]/ R j m)
                  =[ funτ (hi j) m k t ]
                    ⟦ t ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ D′ j k {k<j} n)
                  =[ ap (λ f → ⟦ t ⟧ (λ n → fun (hi j {j<i}) n ∘ f n))
                      (funext λ n → (funext (D′=Q′ j k {k<j} n)))
                  ]
                    ⟦ t ⟧ (λ n → fun (hi j) n ∘ Q′ j k {k<j} n ∘ coe (DA=Q n))
                  =[ ap (λ f → ⟦ t ⟧ (λ n → f n ∘ coe (DA=Q n)))
                    (funext λ n → (symm (fun∘Q′ i hi k j {j<i} {k<j} n)))
                  ]
                    ⟦ t ⟧ (λ n → fun (hi k) n ∘ coe (DA=Q n))
                  qed
                ;(τσᵇ j {j<i} k {k<j} a f) → ap (λ f → sup m (a , f))
                  (funext λ n → funext λ b →
                    proof
                      ⟦ f n b ⟧ (λ o → fun (hi k) o ∘ coe (DA=Q o))
                    =[ ap (λ g → ⟦ f n b ⟧ (λ o → g o ∘ coe (DA=Q o)))
                      (funext λ o → fun∘Q′ i hi k j {j<i} {k<j} o)
                    ]
                      ⟦ f n b ⟧ (λ o → fun (hi j) o ∘ Q′ j k {k<j} o ∘ coe (DA=Q o))
                    =[ ap (λ g → ⟦ f n b ⟧ (λ o → fun (hi j {j<i}) o ∘ g o))
                      (symm (funext λ o → funext (D′=Q′ j k {k<j} o)))
                    ]
                      ⟦ f n b ⟧ (λ o → fun (hi j) o ∘ coe (DA=Q o) ∘ D′ j k {k<j} o)
                    =[ symm (funτ (hi j) n k _) ]
                      fun (hi j) n ([ pairᵇ k {k<j} (f n b) ]/ R j n)
                    =[ ap (fun (hi j) n)
                        (symm (trans (τ=[pairᵇ]/R k {k<j} _ _) (coe=== (DA=Q n) _))) ]
                      fun (hi j) n (coe (DA=Q n) (τ A j k {k<j} n (f n b)))
                    qed
                  )
                })

              funτhyp : ∀ m → ∀ᵇ i λ j {j<i} →
                ((t : T (∣D A ∣ j) m)
                → -----------------------------------------------
                funhyp m ([ pairᵇ j {j<i} t ]/ R i m) ==
                ⟦ t ⟧ (λ n → funhyp n ∘ coe (DA=Q n) ∘ D′ i j {j<i} n))
              funτhyp m j {j<i} t = ap ⟦ t ⟧ (funext λ n → funext λ x →
                match (τ-surj j n x) (λ { (∃ᵇi k {k<j} (∃i t refl)) →
                proof
                  fun (hi j) n (coe (DA=Q n) (τ A j k n t))
                =[ ap (fun (hi j) n)
                  (trans (τ=[pairᵇ]/R k n t) (coe=== (DA=Q n) _)) ]
                  fun (hi j) n ([ pairᵇ k t ]/ R j n)
                =[ funτ (hi j) n k t ]
                  ⟦ t ⟧ (λ o → fun (hi j) o ∘ coe (DA=Q o) ∘ D′ j k o)
                =[ ap (λ f → ⟦ t ⟧ (λ o → fun (hi j {j<i}) o ∘ f o))
                  (funext λ o → funext (D′=Q′ j k o))
                ]
                  ⟦ t ⟧ (λ o → fun (hi j) o ∘ Q′ j k {k<j} o ∘ coe (DA=Q o))
                =[ ap (λ f → ⟦ t ⟧ (λ o → f o ∘ coe (DA=Q o)))
                  (symm (funext (fun∘Q′ i hi k j {j<i} {k<j})))
                ]
                  ⟦ t ⟧ (λ o → fun (hi k) o ∘ coe (DA=Q o))
                =[ refl ]
                  funhyp n ([ pairᵇ k t ]/ R i n)
                =[ ap (funhyp n) (symm (quot.eq (R i n) (τηᵇ j k _))) ]
                  funhyp n ([ pairᵇ j (η n (τ A j k n t)) ]/ R i n)
                =[ ap (funhyp n) (symm (trans (τ=[pairᵇ]/R j _ _) (coe=== (DA=Q n) _))) ]
                  funhyp n (coe (DA=Q n) (τ A i j n (η n (τ A j k n t))))
                qed}))

        recτ : ∀ i → ∀ᵇ i λ j {j<i} →
          ((m : I)
          (t : T (∣D A ∣ j) m)
          → ------------------------------------------
          rec i m (τ A i j {j<i} m t) == ⟦ t ⟧ (rec i ∘ᴵ D′ i j {j<i}))
        recτ i j {j<i} m t =
          proof
            fun (rec' i) m (coe (DA=Q m) (τ A i j {j<i} m t))
          =[ ap (fun (rec' i) m) (trans (τ=[pairᵇ]/R j {j<i} _ _) (coe=== (DA=Q m) _)) ]
            fun (rec' i) m ([ pairᵇ j {j<i} t ]/ R i m)
          =[ funτ (rec' i) m j t ]
            ⟦ t ⟧ (rec i ∘ᴵ D′ i j {j<i})
          qed

        Coconerec : ∀ m → Cocone (D m) (λ i → rec i m)
        Coconerec = λ m i j {j<i} → wf.ind _<_ <iswf P hyp j i {j<i} m
          where
          P : Size → Prop l
          P j =
            (i : Size)
            {j<i : j <ᵇ i}
            (m : I)
            (x : ∣D A ∣ j m)
            → -------------------------------
            rec j m x == rec i m (D′ i j {j<i} m x)

          hyp : ∀ j → (∀ k → (k < j) → P k) → P j
          hyp j h i {j<i} m x = match (τ-surj j m x)
            (λ { (∃ᵇi k {k<j} (∃i t refl)) →
            proof
              rec j m (τ A j k m t)
            =[ recτ j k m t ]
              ⟦ t ⟧ (rec j ∘ᴵ D′ j k)
            =[ ap ⟦ t ⟧ (symm (funext λ n → funext (h k k<j j n))) ]
              ⟦ t ⟧ (rec k)
            =[ ap ⟦ t ⟧ (funext λ n → funext (h k k<j i n)) ]
              ⟦ t ⟧ (rec i ∘ᴵ D′ i k)
            =[ symm (recτ i k m t) ]
              rec i m (τ A i k m t)
            =[ ap (rec i m) (symm (D′τ i j k m t)) ]
              rec i m (D′ i j m (τ A j k m t))
            qed
            })

        -- Existence part of the universal property
        recQWI : QWI ⇁ C
        recQWI m = ∫ (D m) (λ i → rec i m) (Coconerec m)

        homrecQWI : isHom recQWI
        homrecQWI m (a , f) =
          proof
            recQWI m ((∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m)) (((canS {I} {Σ} D m)⁻¹) (a , f)))
          =[ ap (case (((canS {I} {Σ} D m)⁻¹) (a , f)))
            (colimext (S∘ {I} {Σ} D m)
              {f = recQWI m ∘ ∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m)}
              {g = sup m ∘ S' {Σ} recQWI m ∘ canS {I} {Σ} D m}
              lemma
            )
          ]
            sup m (S' {Σ} recQWI m (canS {I} {Σ} D m (((canS {I} {Σ} D m)⁻¹) (a , f))))
          =[ ap (sup m ∘ S' {Σ} recQWI m) (rinv (canS {I} {Σ} D m) (a , f)) ]
            sup m (S' {Σ} recQWI m (a , f))
          qed
          where
          lemma :
            {i : Size}
            (s : S{Σ} (∣D A ∣ i) m)
            → --------------------------------------------
            rec (↑ˢ i) m (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (ι m s))
            == sup m (S' {Σ} (λ n → recQWI n ∘ ν (D n) i) m s)
          lemma {i} (a , f) =
            proof
              rec (↑ˢ i) m (τ A (↑ˢ i) i {<ᵇ↑ˢ} m (σ m (a , (η ∘ᴵ f))))
            =[ recτ (↑ˢ i) i {<ᵇ↑ˢ} _ _ ]
              sup m (a , ((rec (↑ˢ i) ∘ᴵ D′ (↑ˢ i) i {<ᵇ↑ˢ}) ∘ᴵ f))
            =[ ap (λ g → sup m (a , g ∘ᴵ f)) (funext λ n → funext λ z →
              symm (Coconerec n (↑ˢ i) i {<ᵇ↑ˢ} z)
            )]
              sup m (a , (rec i ∘ᴵ f))
            qed

        uniq< :
          (h : QWI ⇁ C)
          (isHomh : isHom h)
          (i : Size)
          → ----------------------------
          rec i == h ∘ᴵ (λ m → ν (D m) i)
        uniq< h isHomh = <ind P hyp
          where
          P : Size → Prop l
          P i = rec i == (λ m → h m ∘ ν (D m) i)

          hyp : ∀ i → (∀ᵇ i λ j {j<i} → P j) → P i
          hyp i hi =
            funext λ m → funext λ x → match (τ-surj i m x) (λ{ (∃ᵇi j {j<i} (∃i t refl)) →
            proof
              rec i m (τ A i j {j<i} m t)
            =[ recτ i j {j<i} m t ]
              ⟦ t ⟧ (rec i ∘ᴵ D′ i j {j<i})
            =[ ap ⟦ t ⟧ (funext λ n → funext λ z → symm (Coconerec n i j {j<i} z)) ]
              ⟦ t ⟧ (rec j)
            =[ ap ⟦ t ⟧ (hi j {j<i}) ]
              ⟦ t ⟧ (h ∘ᴵ λ n → ν (D n) j)
            =[ symm (⟦⟧∘ (λ n → ν (D n) j) h isHomh m t) ]
              h m (⟦ t ⟧ (λ n → ν (D n) j))
            =[ ap (h m) (⟦⟧ν _ _ _ _) ]
              h m (ν (D m) i (τ A i j {j<i} m t))
            qed})

        -- Uniqueness part of the universal property
        uniqQWI :
          (h : QWI ⇁ C)
          (isHomh : isHom h)
          → ----------------
          recQWI == h
        uniqQWI h isHomh =
          --colimext D λ x → ap (case x) (uniq< h isHomh _)
          funext λ m → colimext (D m) (λ x → ap (λ f → f m x) (uniq< h isHomh _))
