module QW.FixedPointsAreQWTypes where

open import QW.SizeIndexedStructure public

----------------------------------------------------------------------
-- Proposition 6.4: given a signature Σ and system of equations ε,
-- there is a type of sizes Size,ssz such that any ◇-fixed point gives
-- an initial algebra for Σ,ε
----------------------------------------------------------------------
module _
  {l : Level}
  (Σ : Sig {l})
  (ε : Syseq Σ)
  where
  private
    Γ = fst ε
    lhs = fst (snd ε)
    rhs = snd (snd ε)
    Ξ = Σ ⊕ Γ
  FxSzAlg→QWType :
    ∃ Size ∶ Set l ,
    ∃ ssz ∶ SizeStructure Size ,
      (let open Colim Size {{ssz}} in
        Inhabited (SizeIdxStruct.FixSizeStruct Σ ε Size {{ssz}} → QWtype Σ ε)
      )
  FxSzAlg→QWType
    with IWISC (mkFam (Op Ξ) (Ar Ξ))
  ... | ∃i (mkFam C F) w
    with IWISC (mkFam (∑ (c , a) ∶ C × (Op Ξ) , (F c → Ar Ξ a)) λ{(_ , f) → ker f})
  ... | ∃i (mkFam C' F') w' =
    ∃i Size (∃i ssz
      (inhab getQWType)
    )
    module _ where
    Size = CocontinuityOfTakingPowers.Size Ξ C F w C' F' w'

    instance
      ssz = CocontinuityOfTakingPowers.ssz Ξ C F w C' F' w'
      upperbounds : UpperBounds {l} _ _
      upperbounds = CocontinuityOfTakingPowers.upperbounds Ξ C F w C' F' w'

    open SizeIdxStruct Σ ε Size {{ssz}} renaming (D to ∣D_∣)
    open Colim Size

    getQWType : SizeIdxStruct.FixSizeStruct {l} Σ ε Size {{ssz}} → QWtype Σ ε
    getQWType (A ∣ δ) =
      mkQWtype QW {{AlgQW}} satQW recQW homrecQW uniqQW
      where

      W : Size → Set l
      W i = Wᵇ (A ↓ i)

      R : ∀ i → W i → W i → Prop l
      R i = Rᵇ (A ↓ i)

      Q : Size → Set l
      Q i = W i / R i

      DA=Q : ∀{i} → ∣D A ∣ i == Q i
      DA=Q {i} = ∧e₁ (δ i)

      τ=[pairᵇ]/R  : ∀{i} → ∀ᵇ j < i ,
        (∀ t → τ A i j t === [ pairᵇ j t ]/ R i)
      τ=[pairᵇ]/R {i} j = ∧e₂ (δ i) j

      W′ : ∀ i → ∏ᵇ j < i , (W j → W i)
      W′ i j (pairᵇ k t) = pairᵇ k t

      Q′ : ∀ i → ∏ᵇ j < i , (Q j → Q i)
      Q′ i j = quot.lift {R = R j}
        (λ z → [ W′ i j z ]/ R i)
        λ{ (τεᵇ k e ρ)   → quot.eq (R i) (τεᵇ k e ρ)
        ; (τηᵇ k l t)   → quot.eq (R i) (τηᵇ k l t)
        ; (τσᵇ k l a f) → quot.eq (R i) (τσᵇ k l a f)
        }

      D′ : ∀ i → ∏ᵇ j < i , (∣D A ∣ j → ∣D A ∣ i)
      D′ i j = τ A i j ∘ η

      τ-surj :
        (i : Size)
        (x : ∣D A ∣ i)
        → ----------------------------------------------
        ∃ᵇ j < i , (∃ t ∶ T (∣D A ∣ j) , τ A i j t == x)
      τ-surj i x =
        match (quot.surjectionmk (R i) (coe DA=Q x))
        λ{(∃i (pairᵇ j t) p) → ∃ᵇi j (∃i t
          (proof
            τ A i j t
          =[ τ=[pairᵇ]/R j t ]
            [ pairᵇ j t ]/ R i
          =[ p ]
            coe DA=Q x
          =[ coe=== DA=Q x ]
            x
          qed))}

      D′=Q′ : ∀ i → ∀ᵇ j < i , (∀ x →
        coe DA=Q (D′ i j x) == Q′ i j (coe DA=Q x))
      D′=Q′ i j x = match (τ-surj j x) (λ {
        (∃ᵇi k (∃i t refl)) →
          proof
            coe DA=Q (τ A i j (η (τ A j k t)))
          =[ coe===  DA=Q _ ]
            τ A i j (η (τ A j k t))
          =[ τ=[pairᵇ]/R j _ ]
            [ pairᵇ j (η (τ A j k t)) ]/ R i
          =[ quot.eq (R i) (τηᵇ j k t) ]
            [ pairᵇ k t ]/ R i
          =[ ap (Q′ i j)
            (symm (trans (τ=[pairᵇ]/R k t) (coe=== DA=Q _))) ]
            Q′ i j (coe DA=Q (τ A j k t))
          qed
        })

      Dact : ∀ i → ∀ᵇ j < i , ∀ᵇ k < j , (∀ z →
        D′ i k z == D′ i j (D′ j k z))
      Dact i j k z =
        proof
          τ A i k (η z)
        =[ τ=[pairᵇ]/R k _ ]
          [ pairᵇ k (η z) ]/ R i
        =[ symm (quot.eq (R i) (τηᵇ j k (η z))) ]
          [ pairᵇ j (η (τ A j k (η z))) ]/ R i
        =[ symm (τ=[pairᵇ]/R j _) ]
          τ A i j (η (τ A j k (η z)))
        qed

      τε : ∀ i → ∀ᵇ j < i ,
        ((e : Op Γ)
        (ρ : Ar Γ e → ∣D A ∣ j)
        → ------------------------------------------------
        τ A i j (T' ρ (lhs e)) == τ A i j (T' ρ (rhs e)))
      τε i j e ρ =
        proof
          τ A i j (T' ρ (lhs e))
        =[ τ=[pairᵇ]/R  j _ ]
          [ pairᵇ j (T' ρ (lhs e)) ]/ R i
        =[ quot.eq (R i) (τεᵇ j e ρ) ]
          [ pairᵇ j (T' ρ (rhs e)) ]/ R i
        =[ symm (τ=[pairᵇ]/R j _) ]
          τ A i j (T' ρ (rhs e))
        qed

      τη : ∀ i → ∀ᵇ j < i ,
        ((z : ∣D A ∣ j)
        → --------------------------
        τ A i j (η z) == D′ i j z)
      τη _ _ _ = refl

      τσ : ∀ i → ∀ᵇ j < i , ∀ᵇ k < j ,
        ((a : Op Σ)
        (f : Ar Σ a → T (∣D A ∣ k))
        → -----------------------------------------
        τ A i k (σ (a , f)) ==
        τ A i j (σ (a , λ b → η (τ A j k (f b)))))
      τσ i j k a f =
        proof
          τ A i k (σ (a , f))
        =[ τ=[pairᵇ]/R k _ ]
          [ pairᵇ k (σ (a , f)) ]/ R i
        =[ quot.eq (R i) (τσᵇ j k a f) ]
          [ pairᵇ j (σ (a , λ b → η (τ A j k (f b)))) ]/ R i
        =[ symm (τ=[pairᵇ]/R j _) ]
          τ A i j (σ (a , λ b → η (τ A j k (f b))))
        qed

      D′τ :  ∀ i → ∀ᵇ j < i , ∀ᵇ k < j , (∀ t →
        D′ i j (τ A j k t) == τ A i k t)
      D′τ i j k t =
        proof
          τ A i j (η (τ A j k t))
        =[ τ=[pairᵇ]/R j _  ]
          [ pairᵇ j (η (τ A j k t)) ]/ R i
        =[ quot.eq (R i) (τηᵇ j k t) ]
          [ pairᵇ k t ]/ R i
        =[ symm (τ=[pairᵇ]/R k _ ) ]
          τ A i k t
        qed

      τD′ :
        (i  j : Size)
        {{p : j <ᵇ i}}
        (t : T (∣D A ∣ j))
        → --------------------------------
        set k ∶ Size , (⋀ q ∶ i <ᵇ k ,
          τ A k j {{<ᵇ<ᵇ{{q = q}}}} t ==
          τ A k i {{q}}  (T' (D′ i j) t))
      τD′ i j {{p}} (η x) =
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
          τ A k j (η x)
        =[ τη k j _ ]
          D′ k j x
        =[ Dact k i j x ]
          D′ k i (D′ i j x)
        =[ symm (τη k i _) ]
          τ A k i (η (D′ i j x))
        qed)
      τD′ i j {{p}} (σ (a , f)) =
        let
          g : Ar Σ a → Size
          g b = el (τD′ i j (f b))

          i<ᵇg : ∀ b → i <ᵇ g b
          i<ᵇg b = ⋀e₁ (pf (τD′ i j (f b)))

          j<ᵇg : ∀ b → j <ᵇ g b
          j<ᵇg b = <ᵇ<ᵇ {{q = i<ᵇg b}}

          e :
            (b : Ar Σ a)
            → ------------------------------------------
            τ A (g b) j {{j<ᵇg b}} (f b) ==
            τ A (g b) i {{i<ᵇg b}} (T' (D′ i j) (f b))
          e b = ⋀e₂ (pf (τD′ i j (f b)))

          k : Size
          k = i ∨ˢ ⋁ˢ (ι₁ a) g

          g<ᵇk : ∀ b → g b <ᵇ k
          g<ᵇk b = <ᵇ<ᵇ {{q = <ᵇ∨ˢr _}} {{<ᵇ⋁ˢ g b}}

          ℓ : Level
          ℓ = l

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
            τ A l j (σ (a , f))
          =[  τσ l k j _ _  ]
            τ A l k (σ (a , λ b → η (τ A k j (f b))))
          =[ ap (λ f' → τ A l k (σ (a , f'))) (funext λ b →
              ap η (symm (D′τ k (g b) {{g<ᵇk b}} j {{j<ᵇg b}} _))) ]
              τ A l k (σ (a , λ b → η (D′ k (g b) {{g<ᵇk b}}
              (τ A (g b) j {{j<ᵇg b}} (f b)))))
          =[ ap (λ h → τ A l k (σ (a , h))) (funext λ b →
              ap (η {ℓ} {Σ} ∘ D′ k (g b) {{g<ᵇk b}}) (e b)) ]
              τ A l k (σ (a , λ b → η (D′ k (g b) {{g<ᵇk b}}
              (τ A (g b) i {{i<ᵇg b}} (T' (D′ i j) (f b))))))
          =[ ap (λ h → τ A l k (σ (a , h))) (funext λ b →
              ap (η {ℓ} {Σ}) (D′τ k (g b) {{g<ᵇk b}} i {{i<ᵇg b}} _ )) ]
              τ A l k (σ (a , λ b → η (τ A k i (T' (D′ i j) (f b)))))
          =[ symm (τσ l k i _ _) ]
            τ A l i (σ (a , λ b → T' (D′ i j) (f b)))
          qed)
          )

      -- Definition of the inital algebra for (Σ, ε) as a colimit
      D : Diag
      vtx D = ∣D A ∣
      edg D = D′
      act D = Dact

      QW : Set l
      QW = colim D

      -- QW is a Σ-algebra
      instance
        canSΣDiso : isIso (canS {Σ} D)
        canSΣDiso = CocontinuityOfPolynomialEndofunctors.Scont Σ Γ Size ssz
          (CocontinuityOfTakingPowers.isIsocan Ξ C F w C' F' w') D
        AlgQW : Alg {l} {Σ} (QW)
        sup {{AlgQW}} = (∫ (S∘ D) φ Coconeφ) ∘ (canS {Σ} D)⁻¹
          module _ where
          φ : (i : Size) → S{l}{Σ}(∣D A ∣ i) → QW
          φ i s = ν D (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (ι s))

          Coconeφ : Cocone (S∘ D) φ
          Coconeφ i j s =
            let
              k : Size
              k = el (τD′ i j (ι s))
              k' : Size
              k' = ↑ˢ i ∨ˢ ↑ˢ j ∨ˢ k
              instance
                i<ᵇk : i <ᵇ k
                i<ᵇk = ⋀e₁ (pf (τD′ i j (ι s)))

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

              e : τ A k j (ι s) == τ A k i (T' (D′ i j) (ι s))
              e = ⋀e₂ (pf (τD′ i j (ι s)))
            in
            proof
              ν D (↑ˢ j) (τ A (↑ˢ j) j {{<ᵇ↑ˢ}} (ι s))
            =[ Coconeν D k' (↑ˢ j) _ ]
              ν D k' (D′ k' (↑ˢ j) ((τ A (↑ˢ j) j {{<ᵇ↑ˢ}} (ι s))))
            =[ ap (ν D k') (D′τ k' (↑ˢ j) j {{<ᵇ↑ˢ}} _) ]
              ν D k' (τ A k' j (ι s))
            =[ ap (ν D k') (symm (D′τ k' k j _)) ]
              ν D k' (D′ k' k (τ A k j (ι s)))
            =[ ap (ν D k' ∘ D′ k' k) e ]
              ν D k' (D′ k' k (τ A k i (T' (D′ i j) (ι s))))
            =[ ap (ν D k') (D′τ k' k i _) ]
              ν D k' (τ A k' i (T' (D′ i j) (ι s)))
            =[ ap (ν D k') (symm (D′τ k' (↑ˢ i) {{↑ˢi<ᵇk'}} i {{<ᵇ↑ˢ}} _)) ]
              ν D k' (D′ k' (↑ˢ i) {{↑ˢi<ᵇk'}}
              (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (T' (D′ i j) (ι s))))
            =[ symm (Coconeν D k' (↑ˢ i) {{↑ˢi<ᵇk'}} _ ) ]
              ν D (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (T' (D′ i j) (ι s)))
            qed

      -- QW satisfies the equational system
      ⟦⟧ν : ∀ i → ∀ᵇ j < i ,
        ((t : T{l}{Σ} (∣D A ∣ j))
        → --------------------------------
        ⟦ t ⟧ (ν D j) == ν D i (τ A i j t))
      ⟦⟧ν i j (η x) =
        proof
          ν D j x
        =[ Coconeν D i j x ]
          ν D i (D′ i j x)
        =[ ap (ν D i) (symm (τη _ _ _)) ]
          ν D i (τ A i j (η x))
        qed
      ⟦⟧ν i j (σ (a , f)) =
          proof
            ∫ (S∘ D) φ Coconeφ (((canS D)⁻¹)
              (a , λ b → ⟦ f b ⟧ (ν D j)))
          =[ ap (λ g → ∫ (S∘ D) φ Coconeφ (((canS D)⁻¹) (a , g)))
            (funext λ b → ⟦⟧ν i j (f b))
          ]
            ∫ (S∘ {Σ} D) {QW} φ Coconeφ (((canS D)⁻¹) (S' (ν D i) (a , λ b → τ A i j (f b))))
          =[ ap (∫ (S∘ D) φ Coconeφ) canS⁻¹Sν ]
            ∫ (S∘ {Σ} D) {QW} φ Coconeφ (ν (S∘ {Σ} D) i ((a , λ b → τ A i j (f b))))
          =[ refl ]
            ν D (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (T' (τ A i j) (σ (a , η ∘ f))))
          =[ ap (ν D (↑ˢ i)) (symm (τσ (↑ˢ i) i {{<ᵇ↑ˢ}} j _ _)) ]
            ν D (↑ˢ i) (τ A (↑ˢ i) j {{<ᵇ<ᵇ {{q = <ᵇ↑ˢ}}}} (σ (a , f)))
          =[ ap (ν D (↑ˢ i)) (symm (D′τ (↑ˢ i) i {{<ᵇ↑ˢ}} j _)) ]
            ν D (↑ˢ i) (D′ (↑ˢ i) i {{<ᵇ↑ˢ}} (τ A i j (σ (a , f))))
          =[ symm (Coconeν D (↑ˢ i) i {{<ᵇ↑ˢ}} _) ]
            ν D i (τ A i j (σ (a , f)))
          qed
        where
        open CocontinuityOfPolynomialEndofunctors Ξ
        canS⁻¹Sν :
            ((canS D)⁻¹) (S' (ν D i) (a , λ b → τ A i j (f b)))
          ===
            ν (S∘ {Σ} D) i ((a , λ b → τ A i j (f b)))
        canS⁻¹Sν = linv (canS D) _

      satQW : Sat {l} {Σ} {ε} QW
      satQW e ρ with CocontinuityOfTakingPowers.surjcan Ξ C F w C' F' w' (ι₂ e) D ρ
      ... | ∃i i (∃i ρi refl) =
        proof
          ⟦ lhs e ⟧ (ν D i ∘ ρi)
        =[ symm (⟦T⟧ (lhs e))  ]
          ⟦ T' ρi (lhs e) ⟧ (ν D i)
        =[ ⟦⟧ν  (↑ˢ i) i {{<ᵇ↑ˢ}} _ ]
          ν D (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (T' ρi (lhs e)))
        =[ ap (ν D (↑ˢ i)) (τε (↑ˢ i) i {{<ᵇ↑ˢ}} _ _) ]
          ν D (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (T' ρi (rhs e)))
        =[ symm (⟦⟧ν  (↑ˢ i) i {{<ᵇ↑ˢ}} _ ) ]
          ⟦ T' ρi (rhs e) ⟧ (ν D i)
        =[ ⟦T⟧ (rhs e) ]
          ⟦ rhs e ⟧ (ν D i ∘ ρi)
        qed

      -- Universal property of QW
      module _
        {C   : Set l}
        {{AlgC  : Alg C}}
        (satC : Sat {l} {Σ} {ε} C)
        where
        rec : ∀ i → ∣D A ∣ i → C
        rec = λ i → fun (rec' i) ∘ coe DA=Q
          module _ where
          record Fun (i : Size) : Set l where
            field
              fun   : W i / R i → C
              funτ : ∀ᵇ j < i ,
                ((t : T (∣D A ∣ j))
                → ---------------------------------
                fun ([ pairᵇ j t ]/ R i) ==
                ⟦ t ⟧ (fun ∘ coe DA=Q ∘ D′ i j))
          open Fun public

          fun∘Q′ :
            (i : Size)
            (hi : ∏ᵇ j < i , Fun j)
            (k j : Size)
            {{_ : j <ᵇ i}}
            {{_ : k <ᵇ j}}
            → -------------------------------
            fun (hi k) == fun (hi j) ∘ Q′ j k
          fun∘Q′ i hi = wf.ind _<_ <iswf P
            λ k hk → hyp k (λ l {{l<ᵇk}} → hk l (<prf l<ᵇk))
            where
            P : Size → Prop l
            P k =
              (j : Size)
              {{_ : j <ᵇ i}}
              {{_ : k <ᵇ j}}
              → -------------------------------
              fun (hi k) == fun (hi j) ∘ Q′ j k

            hyp : ∀ k → (∀ᵇ l < k , P l) → P k
            hyp k hk j = funext (quot.ind (R k)
              (λ z → fun (hi k) z == fun (hi j) (Q′ j k z))
              (λ{(pairᵇ l t) →
                proof
                  fun (hi k) ([ pairᵇ l t ]/ R k)
                =[ funτ (hi k) l t ]
                  ⟦ t ⟧ (fun (hi k) ∘ coe DA=Q ∘ D′ k l)
                =[ ap (λ f → ⟦ t ⟧ (fun (hi k) ∘ f))
                  (funext (D′=Q′ k l)) ]
                  ⟦ t ⟧ (fun (hi k) ∘ Q′ k l ∘ coe DA=Q)
                =[ ap (λ f → ⟦ t ⟧ (f ∘ coe DA=Q))
                  (symm (hk l k)) ]
                  ⟦ t ⟧ (fun (hi l) ∘ coe DA=Q)
                =[ ap (λ f → ⟦ t ⟧ (f ∘ coe DA=Q)) (hk l j) ]
                  ⟦ t ⟧ (fun (hi j) ∘ Q′ j l ∘ coe DA=Q)
                =[ ap (λ f → ⟦ t ⟧ (fun (hi j) ∘ f))
                  (symm (funext (D′=Q′ j l))) ]
                  ⟦ t ⟧ (fun (hi j) ∘ coe DA=Q ∘ D′ j l)
                =[ symm (funτ (hi j) l t) ]
                  fun (hi j) ([ pairᵇ l t ]/ R j)
                qed}))

          rec' : ∀ i → Fun i
          rec' = <rec Fun hyp
            where
            hyp : ∀ i → (∏ᵇ j < i , Fun j) → Fun i
            hyp i hi = record { fun = funhyp ; funτ = funτhyp }
              where
              funhyp : W i / R i → C
              funhyp = quot.lift {R = R i}
                (λ{(pairᵇ j t) → ⟦ t ⟧ (fun (hi j) ∘ coe DA=Q)})
                (λ{(τεᵇ j e ρ) →
                  proof
                    ⟦ T' ρ (lhs e) ⟧ (fun (hi j) ∘ coe DA=Q)
                  =[ ⟦T⟧ (lhs e) ]
                    ⟦ lhs e ⟧ (fun (hi j) ∘ coe DA=Q ∘ ρ)
                  =[ satC e (fun (hi j) ∘ coe DA=Q ∘ ρ) ]
                    ⟦ rhs e ⟧ (fun (hi j) ∘ coe DA=Q ∘ ρ)
                  =[ symm ( ⟦T⟧ (rhs e)) ]
                    ⟦ T' ρ (rhs e) ⟧ (fun (hi j) ∘ coe DA=Q)
                  qed
                ;(τηᵇ j k t) →
                  proof
                    fun (hi j) (coe DA=Q (τ A j k t))
                  =[ ap (fun (hi j))
                      (trans (τ=[pairᵇ]/R k t) (coe=== DA=Q _)) ]
                    fun (hi j) ([ pairᵇ k t ]/ R j)
                  =[ funτ (hi j) k t ]
                    ⟦ t ⟧ (fun (hi j) ∘ coe DA=Q ∘ D′ j k)
                  =[ ap (λ f → ⟦ t ⟧ (fun (hi j) ∘ f))
                      (funext (D′=Q′ j k)) ]
                    ⟦ t ⟧ (fun (hi j) ∘ Q′ j k ∘ coe DA=Q)
                  =[ ap (λ f → ⟦ t ⟧ (f ∘ coe DA=Q))
                    (symm (fun∘Q′ i hi k j)) ]
                    ⟦ t ⟧ (fun (hi k) ∘ coe DA=Q)
                  qed
                ;(τσᵇ j k a f) → ap (λ f → sup (a , f)) (funext λ b →
                  proof
                    ⟦ f b ⟧ (fun (hi k) ∘ coe DA=Q)
                  =[ ap (λ g → ⟦ f b ⟧ (g ∘ coe DA=Q))
                      (fun∘Q′ i hi k j)  ]
                    ⟦ f b ⟧ (fun (hi j) ∘ Q′ j k ∘ coe DA=Q)
                  =[ ap (λ g → ⟦ f b ⟧ (fun (hi j) ∘ g))
                      (symm (funext (D′=Q′ j k))) ]
                    ⟦ f b ⟧ (fun (hi j) ∘ coe DA=Q ∘ D′ j k)
                  =[ symm (funτ (hi j) k _) ]
                    fun (hi j) ([ pairᵇ k (f b) ]/ R j)
                  =[ ap (fun (hi j))
                      (symm (trans (τ=[pairᵇ]/R k _) (coe=== DA=Q _))) ]
                    fun (hi j) (coe DA=Q (τ A j k (f b)))
                  qed)
                })

              funτhyp : ∀ᵇ j < i ,
                ((t : T (∣D A ∣ j))
                → ------------------------------------
                funhyp ([ pairᵇ j t ]/ R i) ==
                ⟦ t ⟧ (funhyp ∘ coe DA=Q ∘ D′ i j))
              funτhyp j t = ap ⟦ t ⟧ (funext λ x →
                match (τ-surj j x) (λ{(∃ᵇi k (∃i t refl)) →
                proof
                  fun (hi j) (coe DA=Q (τ A j k t))
                =[ ap (fun (hi j))
                  (trans (τ=[pairᵇ]/R k t) (coe=== DA=Q _)) ]
                  fun (hi j) ([ pairᵇ k t ]/ R j)
                =[ funτ (hi j) k t ]
                  ⟦ t ⟧ (fun (hi j) ∘ coe DA=Q ∘ D′ j k)
                =[ ap (λ f → ⟦ t ⟧ (fun (hi j) ∘ f))
                  (funext (D′=Q′ j k)) ]
                  ⟦ t ⟧ (fun (hi j) ∘ Q′ j k ∘ coe DA=Q)
                =[ ap (λ f → ⟦ t ⟧ (f ∘ coe DA=Q))
                  (symm (fun∘Q′ i hi k j)) ]
                  ⟦ t ⟧ (fun (hi k) ∘ coe DA=Q)
                =[ refl ]
                  funhyp ([ pairᵇ k t ]/ R i)
                =[ ap funhyp (symm (quot.eq (R i) (τηᵇ j k _))) ]
                  funhyp ([ pairᵇ j (η (τ A j k t)) ]/ R i)
                =[ ap funhyp (symm (trans (τ=[pairᵇ]/R j _) (coe=== DA=Q _))) ]
                  funhyp (coe DA=Q (τ A i j (η (τ A j k t))))
                qed}))

        recτ : ∀ i → ∀ᵇ j < i ,
          ((t : T (∣D A ∣ j))
          → ------------------------------------------
          rec i (τ A i j t) == ⟦ t ⟧ (rec i ∘ D′ i j))
        recτ i j t =
          proof
            fun (rec' i) (coe DA=Q (τ A i j t))
          =[ ap (fun (rec' i)) (trans (τ=[pairᵇ]/R j _) (coe=== DA=Q _)) ]
            fun (rec' i) ([ pairᵇ j t ]/ R i)
          =[ funτ (rec' i) j t ]
            ⟦ t ⟧ (rec i ∘ D′ i j)
          qed

        Coconerec : Cocone D rec
        Coconerec = λ i j → wf.ind _<_ <iswf P hyp j i
          where
          P : Size → Prop l
          P j =
            (i : Size)
            {{_ : j <ᵇ i}}
            (x : ∣D A ∣ j)
            → --------------------------
            rec j x == rec i (D′ i j x)

          hyp : ∀ j → (∀ k → (k < j) → P k) → P j
          hyp j h i {{j<ᵇi}} x = match (τ-surj j x)
            (λ {(∃ᵇi k {{k<ᵇj}} (∃i t refl)) →
            proof
              rec j (τ A j k t)
            =[ recτ j k t ]
              ⟦ t ⟧ (rec j ∘ D′ j k)
            =[ ap ⟦ t ⟧ (symm (funext (h k (<prf k<ᵇj) j))) ]
              ⟦ t ⟧ (rec k)
            =[ ap ⟦ t ⟧ (funext (h k (<prf k<ᵇj) i)) ]
              ⟦ t ⟧ (rec i ∘ D′ i k)
            =[ symm (recτ i k t) ]
              rec i (τ A i k t)
            =[ ap (rec i) (symm (D′τ i j k t)) ]
              rec i (D′ i j (τ A j k t))
            qed
            })

        -- Existence part of the universal property
        recQW : QW → C
        recQW = ∫ D rec Coconerec

        homrecQW : isHom recQW
        homrecQW (a , f) =
          proof
            recQW ((∫ (S∘ D) φ Coconeφ) (((canS D)⁻¹) (a , f)))
          =[ ap (case (((canS D)⁻¹) (a , f)))
            (colimext (S∘ D)
            {f = recQW ∘ ∫ (S∘ D) φ Coconeφ}
            {g = sup ∘ S' recQW ∘ canS D} lemma) ]
            sup (S' recQW (canS D (((canS D)⁻¹) (a , f))))
          =[ ap (sup ∘ S' recQW) (rinv (canS D) (a , f)) ]
            sup (S' recQW (a , f))
          qed
          where
          --open Continuous Σ Γ lhs rhs D

          lemma :
            {i : Size}
            (s : S{l}{Σ} (∣D A ∣ i))
            → --------------------------------------------------------------------
            rec (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (ι s)) == sup (S' (recQW ∘ ν D i) s)
          lemma {i} (a , f) =
            proof
              rec (↑ˢ i) (τ A (↑ˢ i) i {{<ᵇ↑ˢ}} (σ (a , η ∘ f)))
            =[ recτ (↑ˢ i) i {{<ᵇ↑ˢ}} _ ]
              sup (a , rec (↑ˢ i) ∘ D′ (↑ˢ i) i {{<ᵇ↑ˢ}} ∘ f)
            =[ ap (λ g → sup (a , g ∘ f)) (funext λ z →
              symm (Coconerec (↑ˢ i) i {{<ᵇ↑ˢ}} z)) ]
              sup (a , rec i ∘ f)
            qed

        uniq< :
          (h : QW → C)
          (isHomh : isHom h)
          (i : Size)
          → ----------------
          rec i == h ∘ ν D i
        uniq< h isHomh = <ind P hyp
          where
          P : Size → Prop l
          P i = rec i == h ∘ ν D i

          hyp : ∀ i → (∀ᵇ j < i , P j) → P i
          hyp i hi =
            funext λ x →
            match (τ-surj i x) (λ{(∃ᵇi j (∃i t refl)) →
            proof
              rec i (τ A i j t)
            =[ recτ i j t ]
              ⟦ t ⟧ (rec i ∘ D′ i j)
            =[ ap ⟦ t ⟧ (funext λ z → symm (Coconerec i j z)) ]
              ⟦ t ⟧ (rec j)
            =[ ap ⟦ t ⟧ (hi j) ]
              ⟦ t ⟧ (h ∘ ν D j)
            =[ symm (⟦⟧∘ (ν D j) h isHomh t) ]
              h (⟦ t ⟧ (ν D j))
            =[ ap h (⟦⟧ν _ _ _) ]
              h (ν D i (τ A i j t))
            qed})

        -- Uniqueness part of the universal property
        uniqQW :
          (h : QW → C)
          (isHomh : isHom h)
          → ----------------
          recQW == h
        uniqQW h isHomh =
          colimext D λ x → ap (case x) (uniq< h isHomh _)
