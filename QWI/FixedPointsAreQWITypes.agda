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

      τ=[pairᵇ]/R  : ∀{i} → ∀ᵇ j < i ,
        (∀ n t → τ A i j n t === [ pairᵇ j t ]/ R i n)
      τ=[pairᵇ]/R {i} j = ∧e₂ (δ i) j

      W′ : ∀ i → ∏ᵇ j < i , (W j ⇁ W i)
      W′ _ _ _ (pairᵇ k t) = pairᵇ k t

      Q′ : ∀ i → ∏ᵇ j < i , (Q j ⇁ Q i)
      Q′ i j n = quot.lift
        {R = R j n}
        (λ z → [ W′ i j n z ]/ R i n)
        λ
          { (τεᵇ k e ρ)   → quot.eq (R i n) (τεᵇ k e ρ)
          ; (τηᵇ k l t)   → quot.eq (R i n) (τηᵇ k l t)
          ; (τσᵇ k l a f) → quot.eq (R i n) (τσᵇ k l a f)
          }

      D′ : ∀ i → ∏ᵇ j < i , (∣D A ∣ j ⇁ ∣D A ∣ i)
      D′ i j = τ A i j ∘ᴵ η

      τ-surj :
        (i : Size)
        (n : I)
        (x : ∣D A ∣ i n)
        → ----------------------------------------------
        ∃ᵇ j < i , (∃ t ∶ T (∣D A ∣ j) n , τ A i j n t == x)
      τ-surj i n x =
        match (quot.surjectionmk (R i n) (coe (DA=Q n) x))
        λ{(∃i (pairᵇ j t) p) → ∃ᵇi j (∃i t
          (proof
            τ A i j n t
          =[ τ=[pairᵇ]/R j n t ]
            [ pairᵇ j t ]/ R i n
          =[ p ]
            coe (DA=Q n) x
          =[ coe=== (DA=Q n) x ]
            x
          qed))}

      D′=Q′ : ∀ i → ∀ᵇ j < i , (∀ n x →
        coe (DA=Q n) (D′ i j n x) == Q′ i j n (coe (DA=Q n) x))
      D′=Q′ i j n x = match (τ-surj j n x) (λ {
        (∃ᵇi k (∃i t refl)) →
          proof
            coe (DA=Q n) (τ A i j n (η n (τ A j k n t)))
          =[ coe===  (DA=Q n) _ ]
            τ A i j n (η n (τ A j k n t))
          =[ τ=[pairᵇ]/R j n _ ]
            [ pairᵇ j (η n (τ A j k n t)) ]/ R i n
          =[ quot.eq (R i n) (τηᵇ j k t) ]
            [ pairᵇ k t ]/ R i n
          =[ ap (Q′ i j n)
            (symm (trans (τ=[pairᵇ]/R k n t) (coe=== (DA=Q n) _))) ]
            Q′ i j n (coe (DA=Q n) (τ A j k n t))
          qed
        })

      Dact : ∀ i → ∀ᵇ j < i , ∀ᵇ k < j , (∀ n z →
        D′ i k n z == D′ i j n (D′ j k n z))
      Dact i j k n z =
        proof
          τ A i k n (η n z)
        =[ τ=[pairᵇ]/R k n _ ]
          [ pairᵇ k (η n z) ]/ R i n
        =[ symm (quot.eq (R i n) (τηᵇ j k (η n z))) ]
          [ pairᵇ j (η n (τ A j k n (η n z))) ]/ R i n
        =[ symm (τ=[pairᵇ]/R j n _) ]
          τ A i j n (η n (τ A j k n (η n z)))
        qed

      τε : ∀ i → ∀ᵇ j < i ,
        (
          (n : I)
          (e : Op Γ n)
          (ρ : Ar Γ n e ⇁ ∣D A ∣ j)
          → ----------------------------------------------------------
          τ A i j n (T' ρ n (lhs n e)) == τ A i j n (T' ρ n (rhs n e))
        )
      τε i j n e ρ =
        proof
          τ A i j n (T' ρ n (lhs n e))
        =[ τ=[pairᵇ]/R j n _ ]
          [ pairᵇ j (T' ρ n (lhs n e)) ]/ R i n
        =[ quot.eq (R i n) (τεᵇ j e ρ) ]
          [ pairᵇ j (T' ρ n (rhs n e)) ]/ R i n
        =[ symm (τ=[pairᵇ]/R j n _) ]
          τ A i j n (T' ρ n (rhs n e))
        qed

      τη : ∀ i → ∀ᵇ j < i ,
        (
          (n : I)
          (z : ∣D A ∣ j n)
          → -----------------------------
          τ A i j n (η n z) == D′ i j n z
        )
      τη _ _ _ _ = refl

      τσ : ∀ i → ∀ᵇ j < i , ∀ᵇ k < j ,
        (
          (m : I)
          (a : Op Σ m)
          (f : Ar Σ m a ⇁ T (∣D A ∣ k))
          → ---------------------------------------------------
          τ A i k m (σ m (a , f)) ==
          τ A i j m (σ m (a , λ n b → η n (τ A j k n (f n b))))
        )
      τσ i j k m a f =
        proof
          τ A i k m (σ m (a , f))
        =[ τ=[pairᵇ]/R k m _ ]
          [ pairᵇ k (σ m (a , f)) ]/ R i m
        =[ quot.eq (R i m) (τσᵇ j k a f) ]
          [ pairᵇ j (σ m (a , λ n b → η n (τ A j k n (f n b)))) ]/ R i m
        =[ symm (τ=[pairᵇ]/R j m _) ]
          τ A i j m (σ m (a , λ n b → η n (τ A j k n (f n b))))
        qed

      D′τ :  ∀ i → ∀ᵇ j < i , ∀ᵇ k < j , (∀ n t →
        D′ i j n (τ A j k n t) == τ A i k n t)
      D′τ i j k n t =
        proof
          τ A i j n (η n (τ A j k n t))
        =[ τ=[pairᵇ]/R j n _ ]
          [ pairᵇ j (η n (τ A j k n t)) ]/ R i n
        =[ quot.eq (R i n) (τηᵇ j k t) ]
          [ pairᵇ k t ]/ R i n
        =[ symm (τ=[pairᵇ]/R k n _) ]
          τ A i k n t
        qed

      τD′ :
        (i  j : Size)
        {{p : j <ᵇ i}}
        (m : I)
        (t : T (∣D A ∣ j) m)
        → --------------------------------
        set k ∶ Size , (⋀ q ∶ i <ᵇ k ,
          τ A k j {{<ᵇ<ᵇ{{q = q}}}} m t ==
          τ A k i {{q}} m (T' (D′ i j) m t))
      τD′ i j {{p}} m (η .m x) =
        let
          k : Size
          k = ↑ˢ i
          instance
            _ : j <ᵇ i
            _ = p
            q : i <ᵇ k
            q = <ᵇ↑ˢ
            _ : j <ᵇ k
            _ = <ᵇ<ᵇ
        in k ∣ ⋀i q
        (proof
          τ A k j m (η m x)
        =[ τη k j m _ ]
          D′ k j m x
        =[ Dact k i j m x ]
          D′ k i m (D′ i j m x)
        =[ symm (τη k i m _) ]
          τ A k i m (η m (D′ i j m x))
        qed)
      τD′ i j {{p}} m (σ _ (a , f)) =
        let
          g : ∑ I (Ar Σ m a) → Size
          g = λ{(n , b) → el (τD′ i j n (f n b))}

          i<ᵇg : ∀ n b → i <ᵇ g (n , b)
          i<ᵇg n b = ⋀e₁ (pf (τD′ i j n (f n b)))

          j<ᵇg : ∀ n b → j <ᵇ g (n , b)
          j<ᵇg n b = <ᵇ<ᵇ {{q = i<ᵇg n b}}

          e :
            (n : I)
            (b : Ar Σ m a n)
            → -------------------------------------------------
            τ A (g(n , b)) j {{j<ᵇg n b}} n (f n b) ==
            τ A (g(n , b)) i {{i<ᵇg n b}} n (T' (D′ i j) n (f n b))
          e n b = ⋀e₂ (pf (τD′ i j n (f n b)))

          k : Size
          k = i ∨ˢ  ⋁ˢ (m , ι₁ a) g

          g<ᵇk : ∀ n b → g(n , b) <ᵇ k
          g<ᵇk n b = <ᵇ<ᵇ
            {{q = <ᵇ∨ˢr _}} {{<ᵇ⋁ˢ g (n , b)}}

          l : Size
          l = ↑ˢ k

          instance
            _ : i <ᵇ k
            _ = <ᵇ∨ˢl _
            _ : k <ᵇ l
            _ = <ᵇ↑ˢ
            q : i <ᵇ l
            q = <ᵇ<ᵇ
        in l ∣ (⋀i q
          (proof
            τ A l j m (σ m (a , f))
          =[  τσ l k j _ _ _  ]
            τ A l k m (σ m (a , λ n b → η n (τ A k j n (f n b))))
          =[ ap (λ f' → τ A l k m (σ m (a , f'))) (funext λ n → funext λ b →
              ap (η n) (symm (D′τ k (g (n , b)) {{g<ᵇk n b}} j {{j<ᵇg n b}} _ _))) ]
            τ A l k m (σ m (a , λ n b → η n (D′ k (g (n , b)) {{g<ᵇk n b}} n
              (τ A (g (n , b)) j {{j<ᵇg n b}} n (f n b)))))
          =[ ap (λ h → τ A l k m (σ m (a , h))) (funext λ n → funext λ b →
              ap (η {Σ} n ∘ D′ k (g (n , b)) {{g<ᵇk n b}} n) (e n b) ) ]
              τ A l k m (σ m (a , λ n b → η n (D′ k (g (n , b)) {{g<ᵇk n b}} n
              (τ A (g (n , b)) i {{i<ᵇg n b}} n (T' (D′ i j) n (f n b))))))
          =[ ap (λ h → τ A l k m (σ m (a , h))) (funext λ n → funext λ b →
              ap (η {Σ} n) (D′τ k (g (n , b)) {{g<ᵇk n b}} i {{i<ᵇg n b}} _ _ )) ]
              τ A l k m (σ m (a , λ n b → η n (τ A k i n (T' (D′ i j) n (f n b)))))
          =[ symm (τσ l k i _ _ _) ]
            τ A l i m (σ m (a , λ n b → T' (D′ i j) n (f n b)))
          qed))

      -- Definition of the inital algebra for (Σ, ε) as a colimit
      D : I → Diag
      vtx (D n) i     = ∣D A ∣ i n
      edg (D n) i j   = D′ i j n
      act (D n) i j k = Dact i j k n

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
          φ i s = ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (ι m s))

          Coconeφ : Cocone (S∘ {I} {Σ} D m) φ
          Coconeφ i j s =
            let
              k : Size
              k = el (τD′ i j m (ι m s))
              k' : Size
              k' = ↑ˢ i ∨ˢ ↑ˢ j ∨ˢ k
              instance
                i<ᵇk : i <ᵇ k
                i<ᵇk = ⋀e₁ (pf (τD′ i j m (ι m s)))

                j<ᵇk : j <ᵇ k
                j<ᵇk = <ᵇ<ᵇ

                ↑ˢj<ᵇk' : ↑ˢ j <ᵇ k'
                ↑ˢj<ᵇk' = <ᵇ<ᵇ {{q = <ᵇ∨ˢr _}} {{<ᵇ∨ˢl _}}

                i<ᵇk' : i <ᵇ k'
                i<ᵇk' = <ᵇ<ᵇ {{q = <ᵇ∨ˢl _}} {{<ᵇ↑ˢ}}

                j<ᵇk' : j <ᵇ k'
                j<ᵇk' = <ᵇ<ᵇ {{q = ↑ˢj<ᵇk'}}{{<ᵇ↑ˢ}}

                k<ᵇk' : k <ᵇ k'
                k<ᵇk' = <ᵇ<ᵇ {{q = <ᵇ∨ˢr _}} {{<ᵇ∨ˢr _}}

                ↑ˢi<ᵇk' : ↑ˢ i <ᵇ k'
                ↑ˢi<ᵇk' = <ᵇ∨ˢl _

              e : τ A k j m (ι m s) == τ A k i m (T' (D′ i j) m (ι m s))
              e = ⋀e₂ (pf (τD′ i j m (ι m s)))
            in
              proof
                ν (D m) (↑ˢ j) (τ A (↑ˢ j) j {{<ᵇ↑ˢ}} m (ι m s))
              =[ Coconeν (D m) k' (↑ˢ j) _ ]
                ν (D m) k' (D′ k' (↑ˢ j) m (τ A (↑ˢ j) j {{<ᵇ↑ˢ}} m (ι m s)))
              =[ ap (ν (D m) k') (D′τ k' (↑ˢ j) j {{<ᵇ↑ˢ}} m _) ]
                ν (D m) k' (τ A k' j m (ι m s))
              =[ ap (ν (D m) k') (symm (D′τ k' k j m _)) ]
                ν (D m) k' (D′ k' k m (τ A k j m (ι m s)))
              =[ ap (ν (D m) k' ∘ D′ k' k m) e ]
                ν (D m) k' (D′ k' k m (τ A k i m (T' (D′ i j) m (ι m s))))
              =[ ap (ν (D m) k') (D′τ k' k i m _) ]
                ν (D m) k' (τ A k' i m (T' (D′ i j) m (ι m s)))
              =[ ap (ν (D m) k') (symm (D′τ k' (↑ˢ i) {{↑ˢi<ᵇk'}} i {{<ᵇ↑ˢ}} m _)) ]
                ν (D m) k' (D′ k' (↑ˢ i) {{↑ˢi<ᵇk'}} m
                (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (T' (D′ i j) m (ι m s))))
              =[ symm (Coconeν (D m) k' (↑ˢ i) {{↑ˢi<ᵇk'}} _ ) ]
                ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (T' (D′ i j) m (ι m s)))
              qed

      -- QWI satisfies the equational system
      ⟦⟧ν : ∀ i → ∀ᵇ j < i , (
        (m : I)
        (t : T{Σ} (∣D A ∣ j) m)
        → --------------------------------
        ⟦ t ⟧ (λ n → ν (D n) j) == ν (D m) i (τ A i j m t)
        )
      ⟦⟧ν i j m (η .m x) =
        proof
          ν (D m) j x
        =[ Coconeν (D m) i j x ]
          ν (D m) i (D′ i j m x)
        =[ ap (ν (D m) i) (symm (τη _ _ _ _)) ]
          ν (D m) i (τ A i j m (η m x))
        qed
      ⟦⟧ν i j m (σ .m (a , f)) =
        proof
          ∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m) (((canS {I} {Σ} D m)⁻¹)
            (a , λ n b → ⟦ f n b ⟧ λ n → ν (D n) j))
        =[ ap (λ g → ∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m) (((canS {I} {Σ} D m)⁻¹) (a , g)))
          (funext λ n → (funext λ b → ⟦⟧ν i j n (f n b)))
        ]
          ∫ (S∘ {I} {Σ} D m) {QWI m} (φ m) (Coconeφ m)
            (((canS {I} {Σ} D m)⁻¹)
              (S' {Σ} (λ n → ν (D n) i) m
                (a , λ n b → τ A i j n (f n b)
              ))
            )
        =[ ap (∫ (S∘ {I} {Σ} D m) (φ m) (Coconeφ m)) canS⁻¹Sν ]
          ∫ (S∘ {I} {Σ} D m) {QWI m} (φ m) (Coconeφ m)
            (ν (S∘ {I} {Σ} D m) i ((a , λ n b → τ A i j n (f n b))))
        =[ refl ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (T' (τ A i j) m (σ m (a , η ∘ᴵ f))))
        =[ ap (ν (D m) (↑ˢ i)) (symm (τσ (↑ˢ i) i {{<ᵇ↑ˢ}} j _ _ _)) ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) j {{<ᵇ<ᵇ {{q = <ᵇ↑ˢ}}}} m (σ m (a , f)))
        =[ ap (ν (D m) (↑ˢ i)) (symm (D′τ (↑ˢ i) i {{<ᵇ↑ˢ}} j _ _)) ]
          ν (D m) (↑ˢ i) (D′ (↑ˢ i) i {{<ᵇ↑ˢ}} m (τ A i j m (σ m (a , f))))
        =[ symm (Coconeν (D m) (↑ˢ i) i {{<ᵇ↑ˢ}} _) ]
          ν (D m) i (τ A i j m (σ m (a , f)))
        qed
        where
        open CocontinuityOfPolynomialEndofunctors Ξ
        canS⁻¹Sν :
            ((canS {I} {Σ} D m)⁻¹) (S' {Σ} (λ n → ν (D n) i) m (a , λ n b → τ A i j n (f n b)))
          ===
            ν (S∘ {I} {Σ} D m) i ((a , λ n b → τ A i j n (f n b)))
        canS⁻¹Sν = linv (canS {I} {Σ} D m) _

      satQWI : Sat {Σ} {ε} QWI
      satQWI m e ρ = match (surjcan (m , ι₂ e) D ρ)
        λ { (∃i i (∃i ρi refl)) →
        proof
          ⟦ lhs m e ⟧ (λ n → ν (D n) i ∘ ρi n)
        =[ symm (⟦T⟧ m (lhs m e))  ]
          ⟦ T' ρi m (lhs m e) ⟧ (λ n → ν (D n) i)
        =[ ⟦⟧ν  (↑ˢ i) i {{<ᵇ↑ˢ}} _ _ ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (T' ρi m (lhs m e)))
        =[ ap (ν (D m) (↑ˢ i)) (τε (↑ˢ i) i {{<ᵇ↑ˢ}} _ _ _) ]
          ν (D m) (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (T' ρi m (rhs m e)))
        =[ symm (⟦⟧ν (↑ˢ i) i {{<ᵇ↑ˢ}} _ _) ]
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
              funτ : ∀ m → ∀ᵇ j < i ,
                ((t : T (∣D A ∣ j) m)
                → ---------------------------------
                fun m ([ pairᵇ j t ]/ R i m) ==
                ⟦ t ⟧ (λ n → (fun n ∘ coe (DA=Q n) ∘ D′ i j n)))
          open Fun public

          fun∘Q′ :
            (i : Size)
            (hi : ∏ᵇ j < i , Fun j)
            (k j : Size)
            {{_ : j <ᵇ i}}
            {{_ : k <ᵇ j}}
            → -------------------------------------------
            ∀ m → fun (hi k) m == fun (hi j) m ∘ Q′ j k m
          fun∘Q′ i hi = wf.ind _<_ <iswf P
            λ k hk → hyp k (λ l {{l<ᵇk}} → hk l (<prf l<ᵇk))
            where
            P : Size → Prop l
            P k =
              (j : Size)
              {{_ : j <ᵇ i}}
              {{_ : k <ᵇ j}}
              → -------------------------------------------
              ∀ m → fun (hi k) m == fun (hi j) m ∘ Q′ j k m

            hyp : ∀ k → (∀ᵇ l < k , P l) → P k
            hyp k hk j m = funext (quot.ind (R k m)
              (λ z → fun (hi k) m z == fun (hi j) m (Q′ j k m z))
              (λ{(pairᵇ l t) →
                proof
                  fun (hi k) m ([ pairᵇ l t ]/ R k m)
                =[ funτ (hi k) m l t ]
                  ⟦ t ⟧ (λ n → fun (hi k) n ∘ coe (DA=Q n) ∘ D′ k l n)
                =[ ap (λ f → ⟦ t ⟧ (λ n → fun (hi k) n ∘ f n))
                  (funext (λ n → funext (D′=Q′ k l n)))
                ]
                  ⟦ t ⟧ (λ n → fun (hi k) n ∘ Q′ k l n ∘ coe (DA=Q n))
                =[ ap (λ f → ⟦ t ⟧ (λ n → f n ∘ coe (DA=Q n)))
                  (symm (funext (hk l k)))
                ]
                  ⟦ t ⟧ (λ n → fun (hi l) n ∘ coe (DA=Q n))
                =[ ap (λ f → ⟦ t ⟧ (λ n → f n ∘ coe (DA=Q n)))
                  (funext (hk l j))
                ]
                  ⟦ t ⟧ (λ n → fun (hi j) n ∘ Q′ j l n ∘ coe (DA=Q n))
                =[ ap (λ f → ⟦ t ⟧ (λ n → fun (hi j) n ∘ f n))
                  (symm (funext (λ n → funext ((D′=Q′ j l n)))))
                ]
                  ⟦ t ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ D′ j l n)
                =[ symm (funτ (hi j) m l t) ]
                  fun (hi j) m ([ pairᵇ l t ]/ R j m)
                qed}))

          rec' : ∀ i → Fun i
          rec' = <rec Fun hyp
            where
            hyp : ∀ i → (∏ᵇ j < i , Fun j) → Fun i
            hyp i hi = record { fun = funhyp ; funτ = funτhyp }
              where
              funhyp : ∀ m → W i m / R i m → C m
              funhyp m = quot.lift {R = R i m}
                (λ{(pairᵇ j t) → ⟦ t ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n))})
                (λ{(τεᵇ j e ρ) →
                  proof
                    ⟦ T' ρ m (lhs m e) ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n))
                  =[ ⟦T⟧ m (lhs m e) ]
                    ⟦ lhs m e ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ ρ n)
                  =[ satC m e (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ ρ n) ]
                    ⟦ rhs m e ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ ρ n)
                  =[ symm ( ⟦T⟧ m (rhs m e)) ]
                    ⟦ T' ρ m (rhs m e) ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n))
                  qed
                ;(τηᵇ j k t) →
                  proof
                    fun (hi j) m (coe (DA=Q m) (τ A j k m t))
                  =[ ap (fun (hi j) m)
                      (trans (τ=[pairᵇ]/R k m t) (coe=== (DA=Q m) _)) ]
                    fun (hi j) m ([ pairᵇ k t ]/ R j m)
                  =[ funτ (hi j) m k t ]
                    ⟦ t ⟧ (λ n → fun (hi j) n ∘ coe (DA=Q n) ∘ D′ j k n)
                  =[ ap (λ f → ⟦ t ⟧ (λ n → fun (hi j) n ∘ f n))
                      (funext λ n → (funext (D′=Q′ j k n)))
                  ]
                    ⟦ t ⟧ (λ n → fun (hi j) n ∘ Q′ j k n ∘ coe (DA=Q n))
                  =[ ap (λ f → ⟦ t ⟧ (λ n → f n ∘ coe (DA=Q n)))
                    (funext λ n → (symm (fun∘Q′ i hi k j n)))
                  ]
                    ⟦ t ⟧ (λ n → fun (hi k) n ∘ coe (DA=Q n))
                  qed
                ;(τσᵇ j k a f) → ap (λ f → sup m (a , f))
                  (funext λ n → funext λ b →
                    proof
                      ⟦ f n b ⟧ (λ o → fun (hi k) o ∘ coe (DA=Q o))
                    =[ ap (λ g → ⟦ f n b ⟧ (λ o → g o ∘ coe (DA=Q o)))
                      (funext λ o → fun∘Q′ i hi k j o)
                    ]
                      ⟦ f n b ⟧ (λ o → fun (hi j) o ∘ Q′ j k o ∘ coe (DA=Q o))
                    =[ ap (λ g → ⟦ f n b ⟧ (λ o → fun (hi j) o ∘ g o))
                      (symm (funext λ o → funext (D′=Q′ j k o)))
                    ]
                      ⟦ f n b ⟧ (λ o → fun (hi j) o ∘ coe (DA=Q o) ∘ D′ j k o)
                    =[ symm (funτ (hi j) n k _) ]
                      fun (hi j) n ([ pairᵇ k (f n b) ]/ R j n)
                    =[ ap (fun (hi j) n)
                        (symm (trans (τ=[pairᵇ]/R k _ _) (coe=== (DA=Q n) _))) ]
                      fun (hi j) n (coe (DA=Q n) (τ A j k n (f n b)))
                    qed
                  )
                })

              funτhyp : ∀ m → ∀ᵇ j < i ,
                ((t : T (∣D A ∣ j) m)
                → -----------------------------------------------
                funhyp m ([ pairᵇ j t ]/ R i m) ==
                ⟦ t ⟧ (λ n → funhyp n ∘ coe (DA=Q n) ∘ D′ i j n))
              funτhyp m j t = ap ⟦ t ⟧ (funext λ n → funext λ x →
                match (τ-surj j n x) (λ { (∃ᵇi k (∃i t refl)) →
                proof
                  fun (hi j) n (coe (DA=Q n) (τ A j k n t))
                =[ ap (fun (hi j) n)
                  (trans (τ=[pairᵇ]/R k n t) (coe=== (DA=Q n) _)) ]
                  fun (hi j) n ([ pairᵇ k t ]/ R j n)
                =[ funτ (hi j) n k t ]
                  ⟦ t ⟧ (λ o → fun (hi j) o ∘ coe (DA=Q o) ∘ D′ j k o)
                =[ ap (λ f → ⟦ t ⟧ (λ o → fun (hi j) o ∘ f o))
                  (funext λ o → funext (D′=Q′ j k o))
                ]
                  ⟦ t ⟧ (λ o → fun (hi j) o ∘ Q′ j k o ∘ coe (DA=Q o))
                =[ ap (λ f → ⟦ t ⟧ (λ o → f o ∘ coe (DA=Q o)))
                  (symm (funext (fun∘Q′ i hi k j)))
                ]
                  ⟦ t ⟧ (λ o → fun (hi k) o ∘ coe (DA=Q o))
                =[ refl ]
                  funhyp n ([ pairᵇ k t ]/ R i n)
                =[ ap (funhyp n) (symm (quot.eq (R i n) (τηᵇ j k _))) ]
                  funhyp n ([ pairᵇ j (η n (τ A j k n t)) ]/ R i n)
                =[ ap (funhyp n) (symm (trans (τ=[pairᵇ]/R j _ _) (coe=== (DA=Q n) _))) ]
                  funhyp n (coe (DA=Q n) (τ A i j n (η n (τ A j k n t))))
                qed}))

        recτ : ∀ i → ∀ᵇ j < i ,
          ((m : I)
          (t : T (∣D A ∣ j) m)
          → ------------------------------------------
          rec i m (τ A i j m t) == ⟦ t ⟧ (rec i ∘ᴵ D′ i j))
        recτ i j m t =
          proof
            fun (rec' i) m (coe (DA=Q m) (τ A i j m t))
          =[ ap (fun (rec' i) m) (trans (τ=[pairᵇ]/R j _ _) (coe=== (DA=Q m) _)) ]
            fun (rec' i) m ([ pairᵇ j t ]/ R i m)
          =[ funτ (rec' i) m j t ]
            ⟦ t ⟧ (rec i ∘ᴵ D′ i j)
          qed

        Coconerec : ∀ m → Cocone (D m) (λ i → rec i m)
        Coconerec = λ m i j → wf.ind _<_ <iswf P hyp j i m
          where
          P : Size → Prop l
          P j =
            (i : Size)
            {{_ : j <ᵇ i}}
            (m : I)
            (x : ∣D A ∣ j m)
            → -------------------------------
            rec j m x == rec i m (D′ i j m x)

          hyp : ∀ j → (∀ k → (k < j) → P k) → P j
          hyp j h i {{j<ᵇi}} m x = match (τ-surj j m x)
            (λ { (∃ᵇi k {{k<ᵇj}} (∃i t refl)) →
            proof
              rec j m (τ A j k m t)
            =[ recτ j k m t ]
              ⟦ t ⟧ (rec j ∘ᴵ D′ j k)
            =[ ap ⟦ t ⟧ (symm (funext λ n → funext (h k (<prf k<ᵇj) j n))) ]
              ⟦ t ⟧ (rec k)
            =[ ap ⟦ t ⟧ (funext λ n → funext (h k (<prf k<ᵇj) i n)) ]
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
            rec (↑ˢ i) m (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (ι m s))
            == sup m (S' {Σ} (λ n → recQWI n ∘ ν (D n) i) m s)
          lemma {i} (a , f) =
            proof
              rec (↑ˢ i) m (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} m (σ m (a , (η ∘ᴵ f))))
            =[ recτ (↑ˢ i) i {{<ᵇ↑ˢ}} _ _ ]
              sup m (a , ((rec (↑ˢ i) ∘ᴵ D′ (↑ˢ i) i {{<ᵇ↑ˢ}}) ∘ᴵ f))
            =[ ap (λ g → sup m (a , g ∘ᴵ f)) (funext λ n → funext λ z →
              symm (Coconerec n (↑ˢ i) i {{<ᵇ↑ˢ}} z)
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

          hyp : ∀ i → (∀ᵇ j < i , P j) → P i
          hyp i hi =
            funext λ m → funext λ x → match (τ-surj i m x) (λ{ (∃ᵇi j (∃i t refl)) →
            proof
              rec i m (τ A i j m t)
            =[ recτ i j m t ]
              ⟦ t ⟧ (rec i ∘ᴵ D′ i j)
            =[ ap ⟦ t ⟧ (funext λ n → funext λ z → symm (Coconerec n i j z)) ]
              ⟦ t ⟧ (rec j)
            =[ ap ⟦ t ⟧ (hi j) ]
              ⟦ t ⟧ (h ∘ᴵ λ n → ν (D n) j)
            =[ symm (⟦⟧∘ (λ n → ν (D n) j) h isHomh m t) ]
              h m (⟦ t ⟧ (λ n → ν (D n) j))
            =[ ap (h m) (⟦⟧ν _ _ _ _) ]
              h m (ν (D m) i (τ A i j m t))
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
