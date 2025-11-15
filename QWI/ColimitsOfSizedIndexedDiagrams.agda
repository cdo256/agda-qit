module QWI.ColimitsOfSizedIndexedDiagrams where

open import QWI.Size public

----------------------------------------------------------------------
-- Colimits of size-indexed diagrams (section 5.1)
----------------------------------------------------------------------
module Colim
  {l : Level}
  (Size : Set l)
  {{ssz : SizeStructure Size}}
  where
  -- Diagrams in Set
  record Diag : Set (lsuc l) where
    constructor mkDiag
    field
      vtx : Size → Set l
      edg : ∀ i j {j<i : _<ᵇ_ j i} → (vtx j → vtx i)
      act : ∀ i j {j<i : j <ᵇ i} → ∀ k {k<j : k <ᵇ j}
          → (∀ x → edg i k {<ᵇ<ᵇ j<i k<j} x
                == edg i j {j<i} (edg j k {k<j} x))
  open Diag public

  -- Cocones under the diagram
  Cocone :
    (D : Diag)
    {C : Set l}
    (f : ∀ i  → vtx D i → C)
    → ----------------------
    Prop l
  Cocone D f =
    ∀ i j {j<i : j <ᵇ i} → (∀ x → f j x == f i (edg D i j {j<i} x))

  -- Colimits
  colim : Diag → Set l
  colim D = (∑ i ∶ Size , vtx D i)/ ≈
    {- We need to define colim D as a quotient by an equivalence
    relation, because the effectiveness of quotients is needed later -}
    module _ where
    data ≈ : (ix, iy : ∑ i ∶ Size , vtx D i) → Prop l where
      mk≈ :
        {i j : Size}
        {x : vtx D i}
        {y : vtx D j}
        (k : Size)
        {i<k : i <ᵇ k}
        {j<k : j <ᵇ k}
        (_ : edg D k i {i<k} x == edg D k j {j<k} y)
        → ------------------------------
        ≈ (i , x) (j , y)

    ≈refl :
      {z z' : ∑ i ∶ Size , vtx D i}
      (_ : z == z')
      → ---------------------------
      ≈ z z'
    ≈refl {i , _} refl = mk≈ (↑ˢ i) {<ᵇ↑ˢ} {<ᵇ↑ˢ} refl

    ≈symm :
      {(i , x) (j , y) : ∑ i ∶ Size , vtx D i}
      → --------------------------------------
      ≈ (i , x) (j , y) → ≈ (j , y) (i , x)
    ≈symm (mk≈ k p) = mk≈ k (symm p)

    ≈trans :
      {(i , x) (j , y) (k , z) : ∑ i ∶ Size , vtx D i}
      (_ : ≈ (j , y) (k , z))
      (_ : ≈ (i , x) (j , y))
      → ----------------------------------------------
      ≈ (i , x) (k , z)
    ≈trans {i , x} {j , y} {k , z}
           (mk≈ m {i<m} {j<m} e')
           (mk≈ l {i<l} {j<l} e) =
      let
        n : Size
        n = l ∨ˢ m
        i<n : i <ᵇ n
        i<n = <ᵇ<ᵇ (<ᵇ∨ˢl m) i<l
        j<n : j <ᵇ n
        j<n = <ᵇ<ᵇ (<ᵇ∨ˢl _) j<l
        k<n : k <ᵇ n
        k<n = <ᵇ<ᵇ (<ᵇ∨ˢr _) j<m
      in
      mk≈ n
        (proof
          edg D n i {i<n} x
        =[ act D n l {<ᵇ∨ˢl _} i x ]
          edg D n l {<ᵇ∨ˢl _} (edg D l i x)
        =[ ap (edg D n l {<ᵇ∨ˢl _}) e ]
          edg D n l {<ᵇ∨ˢl _} (edg D l j y)
        =[ symm (act D n l {<ᵇ∨ˢl _} j y) ]
          edg D n j y
        =[ act D n m {<ᵇ∨ˢr _} j y ]
          edg D n m {<ᵇ∨ˢr _} (edg D m j y)
        =[ ap (edg D n m {<ᵇ∨ˢr _}) e' ]
          edg D n m {<ᵇ∨ˢr _} (edg D m k z)
        =[ symm (act D n m {<ᵇ∨ˢr _} k z) ]
          edg D n k z
        qed)

  -- The universal cocone
  ν :
    (D : Diag)
    (i : Size)
    → -------------
    vtx D i → colim D
  ν D i x = [ (i , x) ]/ ≈ D

  Coconeν : (D : Diag) → Cocone D (ν D)
  Coconeν D i j {j<i} x =
    quot.eq (≈ D)
      (mk≈ (↑ˢ i) {<ᵇ<ᵇ <ᵇ↑ˢ j<i} {<ᵇ↑ˢ}
        (act D (↑ˢ i) i {<ᵇ↑ˢ} j x))

  -- Universal property of the colimit
  ∫ :
    (D : Diag)
    {C : Set l}
    (f : ∀ i → vtx D i → C)
    (Coconef : Cocone D f)
    → ---------------------
    colim D → C
  ∫ D f Coconef = quot.lift {R = ≈ D}
    (λ{(i , x) →  f i x})
    λ{ {i , x} {j , y} (mk≈ k e) →
      proof
        f i x
      =[ Coconef k i x ]
        f k (edg D k i x)
      =[ ap (f k) e ]
        f k (edg D k j y)
      =[ symm (Coconef k j y) ]
        f j y
      qed}

  colimext :
    (D : Diag)
    {C : Set l}
    {f g : colim D → C}
    (_ : ∀{i} x → f (ν D i x) == g (ν D i x))
    → ---------------------------------------
    f == g
  colimext D e =
    funext (quot.ind (≈ D) _ (λ{(_ , x) → e x}))

  νkernel :
    {D D' : Diag}
    {i i' : Size}
    {x : vtx D i}
    {x' : vtx D' i'}
    (_ : D == D')
    (_ : ν D i x === ν D' i' x')
    → ---------------------------------------------
    ∃ j ∶ Size , ⋀ p ∶ i <ᵇ j , ⋀ p' ∶ i' <ᵇ j ,
      (edg D j i {p} x === edg D' j i' {p'} x')
  νkernel {D} refl e =
    match (quot-eff.prop (≈ D) (≈refl D) (≈symm D) (≈trans D) e)
    λ{(mk≈ j {p} {p'} e) → ∃i j (⋀i p (⋀i p' e))}

  -- Preservation of colimits by polynomial endofunctors (Definition 5.9)
  module _
    {I : Set l}
    where
    open Slice I
    -- Preservation of colimits by taking a power (Definition 5.6)
    infix 4 _⟶ᴵ_
    _⟶ᴵ_ : Setᴵ l → (I → Diag) → Diag -- Power diagrams (5.17)
    vtx (X ⟶ᴵ D) i         = ∀ n → X n → vtx (D n) i
    edg (X ⟶ᴵ D) i j f n x = edg (D n) i j (f n x)
    act (X ⟶ᴵ D) i j k {k<j} f   =
      funext λ n → funext λ x → act (D n) i j k {k<j} (f n x)

    -- E : ∀ i j → {j<i : j <ᵇ i} → (V j → V i)
    -- E i j {j<i} (a , f) = (a , λ b → edg D i j {j<i} (f b))

    -- A : ∀ i j {j<i : j <ᵇ i} → ∀ k {k<j : k <ᵇ j} → (∀ x →
    --     E i k {<ᵇ<ᵇ j<i k<j} x == E i j {j<i} (E j k {k<j} x))
    -- A i j {j<i} k {k<i} (a , f) =
    --   ap {B = λ _ → S{l}{Σ} (vtx D i)} (a ,_)
    --   (funext λ b → act D i j {j<i} k {k<i} (f b))

    can : -- The associated canonical function (5.18)
      (X : Setᴵ l)
      (D : I → Diag)
      → ------------------------------
      colim (X ⟶ᴵ D) → (X ⇁ colim ∘ D)
    can X D = quot.lift {R = ≈ (X ⟶ᴵ D)}
      (λ{(i , f) n x → ν (D n) i (f n x)})
      λ{ {i , f} {j , g} (mk≈ k e) → funext λ n → funext λ x →
        proof
          ν (D n) i (f n x)
        =[ Coconeν (D n)  k i (f n x) ]
          ν (D n) k (edg (D n) k i (f n x))
        =[ ap (λ h → ν (D n) k (h n x)) e ]
          ν (D n) k (edg (D n) k j (g n x))
        =[ symm (Coconeν (D n) k j (g n x)) ]
          ν (D n) j (g n x)
        qed}

    module _
      {Σ : Sig}
      where
      S∘ : (I → Diag) → (I → Diag)
      S∘ D m = mkDiag V E A
        where
        V : Size → Set l
        V i = S{Σ} (λ n → vtx (D n) i) m

        E : (i : Size) → ∏ᵇ i λ j {j<i} → (V j → V i)
        E i j {j<i} (a , f) = (a , λ n b → edg (D n) i j {j<i} (f n b))

        A : ∀ i → ∀ᵇ i λ j {j<i} → ∀ᵇ j λ k {k<j} → (∀ x →
            E i k {<ᵇ<ᵇ j<i k<j} x == E i j {j<i} (E j k {k<j} x))
        A i j k (a , f) =
          proof
            (a , (λ n b → edg (D n) i k (f n b)))
          =[ ap
            {B = λ _ → S{Σ} (λ n → vtx (D n) i) m}
            (λ lhsrhs → (a , (λ n b → lhsrhs n b)))
            (funext (λ n → funext (λ b → act (D n) i j k (f n b))))
          ]
            (a , (λ n b → edg (D n) i j (edg (D n) j k (f n b))))
          qed

      canS : -- the associated canonical function (5.27)
        (D : I → Diag)
        (n : I)
        → ------------------------------------
        colim (S∘ D n) → S{Σ} (colim ∘ D) n
      canS D n = ∫ (S∘ D n) canSf CoconecanSf
        module _ where
        canSf : ∀ i → S{Σ}(λ m → vtx (D m) i) n → S{Σ}(colim ∘ D) n
        canSf i = S'{Σ} (λ m → ν (D m) i) n

        CoconecanSf : Cocone (S∘ D n) canSf
        CoconecanSf i j s =
          ap (λ f → S'{Σ} f n s)
            (funext λ m → funext (Coconeν (D m) i j))

----------------------------------------------------------------------
-- Cocontinuity of taking powers (Theorem 5.7)
----------------------------------------------------------------------
module CocontinuityOfTakingPowers
  {l : Level}
  (I : Set l)
  -- (Σ : Slice.Sig I)
  (A : Set l)
  (B : A → I → Set l)
  where
  ∑B : A → Set l
  ∑B a = ∑ I (B a)
  open Slice I
  theorem :
    ∃ Size ∶ Set l ,
    ∃ ssz ∶ SizeStructure Size ,
     (let open Colim Size {{ssz}} in
      (a : A)
      (D : I → Diag)
      → ----------------------------
      isIso (can (B a) D)           )
  theorem
    with IWISC (mkFam A ∑B)
  ... | ∃i (mkFam C F) w
    with IWISC (mkFam (∑ (c , a) ∶ C × A , (F c → ∑B a))
      λ{(_ , f) → ker f})
  ... | ∃i (mkFam C' F') w' =
    ∃i Size (∃i ssz isIsocan)
    module Inner where
    ------------------------------------------------------------------
    -- Proof of part (1) : to prove the theorem we use the size
    -- associated (as in Lemma 5.5) with the following unindexed
    -- signature
    ------------------------------------------------------------------
    private
      Σ : Unindexed.Sig{l}
      Σ = Unindexed.mkSig A ∑B

      data OpΨ : Set l where
        in₁ : C → OpΨ
        in₂ : C' → OpΨ
        in₃ : A → OpΨ

      ArΨ : OpΨ → Set l
      ArΨ (in₁ c)  = F c
      ArΨ (in₂ c') = F' c'
      ArΨ (in₃ a)  = ∑B a

      Ψ : Unindexed.Sig{l}
      Ψ = Unindexed.mkSig OpΨ ArΨ

    Size : Set l
    Size = Sz Ψ

    ssz : SizeStructure Size
    ssz = SizeStructureSize {Σ = Ψ}

    -- Size = Sz Ψ has upper bounds for arities in Σ
    module _ where
      open Plump (SizeSig Ψ)
      upperbounds : UpperBounds {Σ = Ψ} Σ
      ⋁ˢ   {{upperbounds}} a f = Unindexed.sup (ι₂ (ι₂ (in₃ a)) , f)
      <⋁ˢ  {{upperbounds}} f x = ≺sup x (≤refl (f x))
      <ᵇ⋁ˢ {{upperbounds}} f x = <⋁ˢ f x

    open Colim Size
    module _ (a : A)(D : I → Diag {{ssz}}) where
      qD : (∑ n ∶ I , ∑ Size (vtx (D n))) → ∑ I (colim ∘ D)
      qD (n , i , x) = (n , quot.mk (≈ (D n)) (i , x))
      surjectionqD : surjection qD
      surjectionqD (n , z) with quot.surjectionmk (≈ (D n)) z
      ... | ∃i i refl = ∃i (n , i) refl
      ----------------------------------------------------------------
      -- Property (5.19)
      ----------------------------------------------------------------
      injcan :
        {i j : Size}
        (f : ∀ n → B a n → vtx (D n) i)
        (g : ∀ n → B a n → vtx (D n) j)
        (e : (λ n x → ν (D n) i (f n x)) ==
          (λ n x → ν (D n) j (g n x))      )
        → ----------------------------------------
        ∃ k ∶ Size , ⋀ p ∶ (_<ᵇ_ i k) , ⋀ q ∶ j <ᵇ k ,
          (∀ n x →
            edg (D n) k i {p} (f n x) ==
            edg (D n) k j {q} (g n x))
      injcan {i} {j} f g e =
        lemma (wAC (mkFam C F) (w a) (λ _ → Size) P Ptotal)
        where
        P : ∑ I (B a) → Size → Prop l
        P (n , x) k =
          ⋀ p ∶ i <ᵇ k ,
          ⋀ q ∶ j <ᵇ k ,
            (edg (D n) k i {p} (f n x) ==
             edg (D n) k j {q} (g n x))

        Ptotal : (nx : ∑ I (B a)) → ∃ k ∶ Size , P nx k
        Ptotal (n , x) = νkernel refl (ap (λ e' → e' n x) e)

        lemma :
          ( ∃ c ∶ C
          , ∃ p ∶ (F c → ∑ I (B a))
          , ∃ s ∶ (F c → Size)
          , (surjection p ∧ ∀ x' → P (p x')(s x')))
          → ------------------------------------------
          ∃ k ∶ Size , ⋀ u ∶ i <ᵇ k , ⋀ v ∶ j <ᵇ k ,
            (∀ n x →
             edg (D n) k i {u} (f n x) ==
             edg (D n) k j {v} (g n x))
        lemma (∃i c (∃i p (∃i s (∧i surjectionh sp-eq)))) =
          ∃i k (⋀i u (⋀i v λ n x →
            match (surjectionh (n , x)) \ where
              (∃i x' refl) →
                match (sp-eq x') \ where
                  (⋀i i<ᵇsx' (⋀i j<ᵇsx' e')) →
                    proof
                      edg (D n) k i {u} (f n (snd (p x')))
                    =[ act (D n) k (s x') {_} i {_} _ ]
                      edg (D n) k  (s x') {sx'<ᵇk x'}
                     (edg (D n) (s x') i {i<ᵇsx'} (f n (snd (p x'))))
                    =[ ap (edg (D n) k (s x') {sx'<ᵇk x'}) e' ]
                      edg (D n) k  (s x') {sx'<ᵇk x'}
                      (edg (D n) (s x') j {j<ᵇsx'} (g n (snd (p x'))))
                    =[ symm (act (D n) k (s x') {_} j {_} _) ]
                      edg (D n) k j {v} (g n (snd (p x')))
                    qed))
          where
          k : Size
          k = i ∨ˢ j ∨ˢ (⋁ˢ (in₁ c) s)

          u : i <ᵇ k
          u = <ᵇ∨ˢl _

          v : j <ᵇ k
          v = <ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ∨ˢl _)

          sx'<ᵇk : ∀ x' → s x' <ᵇ k
          sx'<ᵇk x' =
            <ᵇ<ᵇ (<ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ∨ˢr _)) (<ᵇ⋁ˢ s x')

      ----------------------------------------------------------------
      -- Proof of part (2): injectivity of the canonical function
      -- colim (X ⟶ D) → (X → colim D)
      ----------------------------------------------------------------
      injectioncan : injection (can (B a) D)
      injectioncan {z} {z'} =
        quot.ind₂ (≈ (B a ⟶ᴵ D)) (≈ (B a ⟶ᴵ D))
          (λ z z' → can (B a) D z == can (B a) D z' → z == z')
          (λ{(i , f) (j , g) e → match (injcan f g e) \ where
            (∃i k (⋀i p (⋀i q e'))) →
              quot.eq (≈ (B a ⟶ᴵ D)) (mk≈ k {p} {q}
              (funext λ n → funext (e' n)))})
          z
          z'

      ----------------------------------------------------------------
      -- Property (5.20)
      ----------------------------------------------------------------
      surjcan :
        (f : B a ⇁ colim ∘ D)
        → ----------------------------------------------
        ∃ i ∶ Size , ∃ f' ∶ (∀ n → B a n → vtx (D n) i),
          f == λ n x → ν (D n) i (f' n x)
      surjcan f = lemma (wAC _ (w a) _ P Ptotal)
       where
        P : ((n , x) : ∑ I (B a)) → (∑ Size (vtx (D n))) → Prop l
        P (n , x) (i , y ) = [ (i , y) ]/ ≈ (D n) == f n x

        Ptotal :
          ((n , x) : ∑ I (B a))
          → --------------------------------------
          ∃ iy ∶ ∑ Size (vtx (D n)) , P (n , x) iy
        Ptotal (n , x) = quot.surjectionmk (≈ (D n)) (f n x)

        lemma :
          (∃ c ∶ C ,
          ∃ p ∶ (F c → ∑ I (B a)),
          ∃ sg ∶ ((z : F c) → ∑ Size (vtx (D (fst (p z))))),
          (surjection p ∧ ∀ z → P (p z)(sg z)))
          → ------------------------------------------------
          ∃ i ∶ Size , ∃ f' ∶ (∀ n → B a n → vtx (D n) i) ,
            f == λ n x → ν (D n) i (f' n x)
        lemma (∃i c (∃i p (∃i sg (∧i surjectionp u)))) =
          lemma' (wAC _ (w' _) _ P' P'total)
          where
          p₁ : F c → I
          p₁ = fst ∘ p

          p₂ : (z : F c) → B a (p₁ z)
          p₂ = snd ∘ p

          s : F c → Size
          s = fst ∘ sg

          g : (z : F c) → vtx (D (p₁ z)) (s z)
          g = snd ∘ sg

          j : Size
          j = ⋁ˢ (in₁ c) s

          s<ᵇj : ∀ z  → s z <ᵇ j
          s<ᵇj z = <ᵇ⋁ˢ s z

          fj : ∀ z → vtx (D (p₁ z)) j
          fj z = edg (D (p₁ z)) j (s z) {s<ᵇj z} (g z)

          νfj=fp : ∀ z → ν (D (p₁ z)) j (fj z) == f (p₁ z) (p₂ z)
          νfj=fp z =
            proof
              ν (D (p₁ z)) j (fj z)
            =[ symm (Coconeν (D (p₁ z)) j (s z) {s<ᵇj z} (g z)) ]
              ν (D (p₁ z)) (s z) (g z)
            =[ u z ]
              f (p₁ z) (p₂ z)
            qed

          P' : ker p → Size → Prop l
          P' ((z , z') ∣ _) k = ⋀ j<ᵇk ∶ j <ᵇ k ,
            edg (D (p₁ z )) k j {j<ᵇk} (fj z ) ===
            edg (D (p₁ z')) k j {j<ᵇk} (fj z')

          P'total : ∀ zz' → ∃ k ∶ Size , P' zz' k
          P'total ((z , z') ∣ pz=pz') =
            match (νkernel e e') λ{(∃i k (⋀i j<ᵇk (⋀i _ e''))) →
            ∃i k (⋀i j<ᵇk e'')}
            where
            e : D (p₁ z) == D(p₁ z')
            e = ap (D ∘ fst) pz=pz'

            e' :
              ν (D (p₁ z)) j (fj z) ===
              ν (D (p₁ z')) j (fj z')
            e' =
              proof
                ν (D (p₁ z)) j (fj z)
              =[ νfj=fp z ]
                f (p₁ z) (p₂ z)
              =[ ap (λ x → f (fst x) (snd x)) pz=pz' ]
                f (p₁ z') (p₂ z')
              =[ symm (νfj=fp z') ]
                ν (D (p₁ z')) j (fj z')
              qed

          lemma' :
            (∃ c' ∶ C' ,
            ∃ p' ∶ (F' c' → ker p),
            ∃ s' ∶ (F' c' → Size),
            (surjection p' ∧ ∀ z → P' (p' z) (s' z)))
            → ----------------------------------------------
            ∃ i ∶ Size , ∃ g' ∶ (∀ n → B a n → vtx (D n) i),
              f == λ n x → ν (D n) i (g' n x)
          lemma' (∃i c' (∃i p' (∃i s' (∧i surjectionp' u)))) =
            ∃i i (∃i g' f=νig')
            where
            i : Size
            i = j ∨ˢ ⋁ˢ (in₂ c') s'

            j<ᵇi : j <ᵇ i
            j<ᵇi = <ᵇ∨ˢl _

            s'<ᵇi : ∀ z' → s' z' <ᵇ i
            s'<ᵇi z' = <ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ⋁ˢ s' z')

            fi : (z : F c) → vtx (D (p₁ z)) i
            fi z = edg (D (p₁ z)) i j {j<ᵇi} (fj z)

            νfi=fp :
              (z : F c)
              → --------------------------------------
              ν (D (p₁ z)) i (fi z) == f (p₁ z) (p₂ z)
            νfi=fp z =
              proof
                ν (D (p₁ z)) i (fi z)
              =[ symm (Coconeν (D (p₁ z)) i j {j<ᵇi} (fj z)) ]
                ν (D (p₁ z)) j (fj z)
              =[ νfj=fp z ]
                f (p₁ z) (p₂ z)
              qed

            p₁' : F' c' → F c
            p₁' z' = fst (el (p' z'))

            p₂' : F' c' → F c
            p₂' z' = snd (el (p' z'))

            G' : ((n , _) : ∑ I (B a)) → vtx (D n) i → Prop l
            G' nx d = ∃ z ∶ F c , (p z == nx) ∧ (fi z === d)

            instance
              ∃!G' : ∀{nx} → ∃! (vtx (D (fst nx)) i) (G' nx)
              ∃!G' {n , x} with surjectionp (n , x)
              ... | ∃i z₂ refl = ∃i (fi z₂) (∧i (∃i z₂ (∧i refl refl))
                λ{d (∃i z₁ (∧i pz₁=pz₂ fiz₁=d)) →
                match (surjectionp' ((z₁ , z₂) ∣ pz₁=pz₂)) \ where
                  (∃i z' p'z'=z₁z₂) →
                    match (u z') \ where
                      (⋀i j<ᵇs'z' e') →
                        proof
                          fi z₂
                        =[ ap (fi ∘ snd ∘ el) (symm p'z'=z₁z₂) ]
                          edg (D (p₁ (p₂' z'))) i j {j<ᵇi} (fj (p₂' z'))
                        =[ act (D (p₁ (p₂' z'))) i (s' z') {s'<ᵇi z'}
                          j {j<ᵇs'z'} _ ]
                          edg (D (p₁ (p₂' z'))) i (s' z') {s'<ᵇi z'}
                          (edg (D (p₁ (p₂' z'))) (s' z') j {j<ᵇs'z'} (fj (p₂' z')))
                        =[ symm (ap₂ (λ 𝕛 d → edg (D 𝕛) i (s' z') {s'<ᵇi z'} d)
                          (ap fst (pf (p' z'))) e') ]
                          edg (D (p₁ (p₁' z'))) i (s' z') {s'<ᵇi z'}
                          (edg (D (p₁ (p₁' z'))) (s' z') j {j<ᵇs'z'} (fj (p₁' z')))
                        =[ symm (act (D (p₁ (p₁' z'))) i (s' z') {s'<ᵇi z'}
                          j {j<ᵇs'z'} _) ]
                          edg (D (p₁ (p₁' z'))) i j {j<ᵇi} (fj (p₁' z'))
                        =[ ap (fi ∘ fst ∘ el) p'z'=z₁z₂ ]
                          fi z₁
                        =[ fiz₁=d ]
                          d
                        qed})

            g' : ∀ n → B a n → vtx (D n) i
            g' n x = the (vtx (D n) i) (G' (n , x))

            f=νig' : f == λ n x → ν (D n) i (g' n x)
            f=νig' = funext λ n → funext λ x →
              match (the-pf (vtx (D n) i) (G' (n , x))) \ where
                (∃i z (∧i pz=nx fiz=g'ix)) →
                  proof
                    f n x
                  =[ ap (λ x → f (fst x) (snd x)) (symm pz=nx) ]
                    f (p₁ z) (p₂ z)
                  =[ symm (νfi=fp z) ]
                    ν (D (p₁ z)) i (fi z)
                  =[ ap₂ (λ n d → ν (D n) i d) (ap fst pz=nx) fiz=g'ix ]
                    ν (D n) i (g' n x)
                  qed

      ----------------------------------------------------------------
      -- Proof of part (3): surjectivity of the canonical function
      -- colim (X ⟶ D) → (X → colim D)
      ----------------------------------------------------------------
      surjectioncan : surjection (can (B a) D)
      surjectioncan f = match (surjcan f) \ where
        (∃i i (∃i fi refl)) → ∃i ([ (i , fi) ]/ ≈ _) refl

      isIsocan =
        bijectionIsIso (can (B a) D)
        (∧i injectioncan surjectioncan)


----------------------------------------------------------------------
-- Cocontinuity of polynomial endofunctors (Corollary 5.10) in a form
-- that is convenient for its use in
-- section 6 (FixedPointsAreQWITypes.agda)
----------------------------------------------------------------------
module CocontinuityOfPolynomialEndofunctors
  {l : Level}
  {I : Set l}
  (Σ : Slice.Sig{l} I)
  (ε : Slice.Syseq{l} I Σ)
  where
  open Slice I
  open Syseq ε

  theorem :
    ∃ Sz ∶ Set l ,
    ∃ sz ∶ SizeStructure Sz , (let open Colim Sz {{sz}} in
      ((D : I → Diag)(n : I) → isIso (canS {Σ = Σ} D n)))
  theorem with
    CocontinuityOfTakingPowers.theorem
     I (∑ I (Op (Σ ⊕ Γ))) (uncurry (Ar (Σ ⊕ Γ)))
  ... | ∃i Size (∃i ssz p) = ∃i Size (∃i ssz Scont)
    module _ where
    open Colim Size
    instance
      _ : SizeStructure Size
      _ = ssz

    Scont : (D : I → Diag)(n : I) → isIso (canS {Σ = Σ} D n)
    Scont D n = ∃i inv' (∧i linv' rinv')
      where
      φ :
        (a : Op Σ n)
        (i : Size) →
        (f : ∀ m → Ar Σ n a m → vtx (D m) i)
        → ----------------------------------
        colim (S∘{Σ = Σ} D n)
      φ a i f = ν (S∘{Σ = Σ} D n) i (a , f)

      Coconeφ : (a : Op Σ n) → Cocone (Ar Σ n a ⟶ᴵ D) (φ a)
      Coconeφ a i j {j<i} f =
        let
          instance
            _ : SizeStructure Size
            _ = ssz
          k : Size
          k = ↑ˢ i
          j<k : j <ᵇ k
          j<k = <ᵇ<ᵇ (<∨ˢl i) j<i
        in
        quot.eq (≈ (S∘{Σ = Σ} D n)) (mk≈ k {j<k} {<∨ˢl i}
          (proof
             edg (S∘{Σ = Σ} D n) k j {j<k} (a , f)
           =[ refl ]
            (a , λ m x → edg (D m) k j (f m x))
           =[ ap {B =  λ _ → S{Σ} (λ m → vtx (D m) k) n}
              (λ g → (a , (λ m x → g m x)))
              (funext λ m → funext λ x → act (D m) k i j (f m x)) ]
             (a , λ m x → edg (D m) k i (edg (D m) i j (f m x)))
           =[ refl ]
             (a , λ m x → edg (D m) k i (edg (Ar Σ n a ⟶ᴵ D) i j f m x))
           =[ refl ]
             edg (S∘{Σ = Σ} D n) k i {<∨ˢl i} (a , edg (Ar Σ n a ⟶ᴵ D) i j f)
           qed))

      c : (a : Op Σ n) → colim (Ar Σ n a ⟶ᴵ D) → colim (S∘{Σ = Σ} D n)
      c a = ∫ (Ar Σ n a ⟶ᴵ D) (φ a) (Coconeφ a)

      lemma : {a : Op Σ n} → canS{Σ = Σ} D n ∘ c a == (a ,_) ∘ can (Ar Σ n a) D
      lemma {a} = colimext (Ar Σ n a ⟶ᴵ D) λ _ → refl

      inv' : S{Σ} (colim ∘ D) n → colim (S∘{Σ = Σ} D n)
      inv' (a , f) = c a (((can (Ar Σ n a) D)⁻¹) f)
        where
        instance
          _ : isIso (can (Ar Σ n a) D)
          _ = p (n , ι₁ a) D

      linv' : (z : colim (S∘{Σ = Σ} D n)) → inv' (canS{Σ = Σ} D n z) == z
      linv' = quot.ind (≈ (S∘ {Σ = Σ} D n)) _ λ{(i , a , f) →
        let instance _ = p (n , ι₁ a) D in
        ap (c a) (linv _ (ν (Ar Σ n a ⟶ᴵ D) i f))}

      rinv' : (s : S{Σ} (colim ∘ D) n) → canS{Σ = Σ} D n (inv' s) == s
      rinv' (a , f) =
        let instance _ = p (n , ι₁ a) D in
        proof
          canS{Σ = Σ} D n (inv' (a , f))
        =[ refl ]
          canS{Σ = Σ} D n (c a (((can (Ar Σ n a) D)⁻¹) f))
        =[ ap (case ((can _ D ⁻¹) f)) lemma ]
          (a , can _ D (((can _ D)⁻¹) f))
        =[ ap (a ,_) (rinv _ f) ]
          (a , f)
        qed
