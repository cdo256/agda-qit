module QW.ColimitsOfSizedIndexedDiagrams where

open import QW.Size public

----------------------------------------------------------------------
-- Colimits of size-indexed diagrams (section 5.1)
----------------------------------------------------------------------
module Colim
  {l : Level}
  (Size : Set l)
  {{_ : SizeStructure Size}}
  where
  -- Diagrams in Set
  record Diag : Set (lsuc l) where
    constructor mkDiag
    field
      vtx : Size → Set l
      edg : ∀ i j {j<i : j <ᵇ i} → (vtx j → vtx i)
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

  -- Preservation of colimits by taking a power (Definition 5.6)
  infix 4 _⟶_
  _⟶_ : Set l → Diag → Diag -- Power diagrams (5.17)
  vtx (X ⟶ D) i       = X → vtx D i
  edg (X ⟶ D) i j {j<i} f x = edg D i j {_} (f x)
  act (X ⟶ D) i j {j<i} k {k<j} f =
    funext λ x → act D i j {j<i} k {k<j} (f x)

  can : -- The associated canonical function (5.18)
    (X : Set l)
    (D : Diag)
    → ---------------------------
    colim (X ⟶ D) → (X → colim D)
  can X D = quot.lift {R = ≈ (X ⟶ D)}
    (λ{(i , f) x → ν D i (f x)})
    λ{ {i , f} {j , g} (mk≈ k e) → funext λ x →
      proof
        ν D i (f x)
      =[ Coconeν D k i (f x) ]
        ν D k (edg D k i (f x))
      =[ ap (λ h → ν D k (h x)) e ]
        ν D k (edg D k j (g x))
      =[ symm (Coconeν D k j (g x)) ]
        ν D j (g x)
      qed}

  -- Preservation of colimits by polynomial endofunctors (Definotion 5.9)
  S∘ : {Σ : Sig{l}} → Diag → Diag
  -- apply the polynomial endofunctor S{Σ} to a diagram (5.26)
  S∘ {Σ} D = mkDiag V E A
    where
    V : Size → Set l
    V i = S{l}{Σ} (vtx D i)

    E : ∀ i j → {j<i : j <ᵇ i} → (V j → V i)
    E i j {j<i} (a , f) = (a , λ b → edg D i j {j<i} (f b))

    A : ∀ i j {j<i : j <ᵇ i} → ∀ k {k<j : k <ᵇ j} → (∀ x →
        E i k {<ᵇ<ᵇ j<i k<j} x == E i j {j<i} (E j k {k<j} x))
    A i j {j<i} k {k<i} (a , f) =
      ap {B = λ _ → S{l}{Σ} (vtx D i)} (a ,_)
      (funext λ b → act D i j {j<i} k {k<i} (f b))

  canS : -- the associated canonical function (5.27)
    {Σ : Sig{l}}
    (D : Diag)
    → ---------------------------
    colim (S∘ D) → S{l}{Σ} (colim D)
  canS {Σ} D = ∫ (S∘ D) canSf CoconecanSf
    module _ where
    canSf : ∀ i → S{l}{Σ}(vtx D i) → S{l}{Σ}(colim D)
    canSf i = S' (ν D i)

    CoconecanSf : Cocone (S∘ D) canSf
    CoconecanSf i j s =
      ap (λ f → S' f s) (funext (Coconeν D i j))

  
Sig→Fam : {l : Level} → Sig {l} → Fam l
Sig→Fam (mkSig op ar) = mkFam op ar

module ConstructiveCocontinuity
  {l : Level}
  (Σ : Sig {l})
  where

  CoverSubTypeFam : (WISC-Cover (Sig→Fam Σ)) → Fam l
  CoverSubTypeFam U = mkFam (∑ (c , a) ∶ C × (Op Σ) , (F c → Ar Σ a)) λ{(_ , f) → ker f}
    where open WISC-Cover U

  theorem :
    (U : WISC-Cover (Sig→Fam Σ))
    (V : WISC-Cover (CoverSubTypeFam U))
    → ------------------------
    ∃ Size ∶ Set l ,
    ∃ ssz ∶ SizeStructure Size ,
      (let open Colim Size {{ssz}} in
        ((a : Op Σ)(D : Diag) → isIso (can (Ar Σ a) D)))
  theorem U V = 
    ∃i Size (∃i ssz isIsocan)
    module _ where
    open WISC-Cover U
    open WISC-Cover V renaming (C to C'; F to F'; w to w')
    ------------------------------------------------------------------
    -- Proof of part (1) : to prove the theorem we use the size
    -- associated (as in Lemma 5.5) with the following signature
    ------------------------------------------------------------------
    private
      data OpΨ : Set l where
        in₁ : C → OpΨ
        in₂ : C' → OpΨ
        in₃ : Op Σ → OpΨ

      ArΨ : OpΨ → Set l
      ArΨ (in₁ c)  = F c
      ArΨ (in₂ c') = F' c'
      ArΨ (in₃ a)  = Ar Σ a

      Ψ : Sig{l}
      Ψ = mkSig OpΨ ArΨ

    Size : Set l
    Size = Sz Ψ

    ssz : SizeStructure Size
    ssz = SizeStructureSize {Σ = Ψ}

    -- Size = Sz Ψ has upper bounds for arities in Σ
    module _ where
      open Plump (SizeSig Ψ)
      upperbounds : UpperBounds Σ Ψ
      ⋁ˢ   {{upperbounds}} a f       = sup (ι₂ (ι₂ (in₃ a)) , f)
      <⋁ˢ  {{upperbounds}} f x       = ≺sup x (≤refl (f x))
      <ᵇ⋁ˢ {{upperbounds}} f x       = <⋁ˢ f x

    open Colim Size

    module _ (a : Op Σ)(D : Diag) where
      X : Set l
      X = Ar Σ a

      qD : ∑ Size (vtx D) → colim D
      qD = quot.mk (≈ D)

      surjectionqD : surjection qD
      surjectionqD = quot.surjectionmk (≈ D)

      ----------------------------------------------------------------
      -- Property (5.19)
      ----------------------------------------------------------------
      injcan :
        {i j : Size}
        (f : X → vtx D i)
        (g : X → vtx D j)
        (e : ν D i ∘ f == ν D j ∘ g)
        → ------------------------------------------
        ∃ k ∶ Size , ⋀ p ∶ i <ᵇ k , ⋀ q ∶ j <ᵇ k ,
          edg D k i {p} ∘ f == edg D k j {q} ∘ g
      injcan {i} {j} f g e =
        lemma (wAC (mkFam C F) (w a) (λ _ → Size) P Ptotal)
        where
        P : X → Size → Prop l
        P x k =
          ⋀ p ∶ i <ᵇ k ,
          ⋀ q ∶ j <ᵇ k ,
            (edg D k i {p} (f x) == edg D k j {q} (g x))

        Ptotal : ∀ x → ∃ k ∶ Size , P x k
        Ptotal x = match
          (quot-eff.prop (≈ D)
            (≈refl D)
            (≈symm D)
            (≈trans D)
            (ap (case x) e))
          λ{(mk≈ k {p} {q} e') → ∃i k (⋀i p (⋀i q e'))}

        lemma :
          ( ∃ c ∶ C
          , ∃ p ∶ (F c → X)
          , ∃ s ∶ (F c → Size)
          , (surjection p ∧ ∀ x' → P (p x')(s x')))
          → ------------------------------------------
          ∃ k ∶ Size , ⋀ u ∶ i <ᵇ k , ⋀ v ∶ j <ᵇ k ,
            edg D k i {u} ∘ f == edg D k j {v} ∘ g
        lemma (∃i c (∃i p (∃i s (∧i surjectionh sp-eq)))) =
          ∃i k (⋀i u (⋀i v (funext (λ
            x → match (surjectionh x) (λ{
            (∃i x' refl) → match (sp-eq x') λ{
            (⋀i i<ᵇsx' (⋀i j<ᵇsx' e')) →
              proof
                edg D k i {u} (f (p x'))
              =[ act D k (s x') {_} i {_} _ ]
                edg D k  (s x') {sx'<ᵇk x'}
                  (edg D (s x') i {i<ᵇsx'} (f (p x')))
              =[ ap (edg D k (s x') {sx'<ᵇk x'}) e' ]
                edg D k  (s x') {sx'<ᵇk x'}
                  (edg D (s x') j {j<ᵇsx'} (g (p x')))
              =[ symm (act D k (s x') {_} j {_} _) ]
                edg D k j {v} (g (p x'))
              qed
            }})
          ))))
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
      injectioncan : injection (can X D)
      injectioncan {z} {z'} = quot.ind₂ (≈ (X ⟶ D)) (≈ (X ⟶ D))
          (λ z z' → can X D z == can X D z' → z == z')
          (λ{(i , f) (j , g) e →
          match (injcan f g e) λ{(∃i k (⋀i p (⋀i q e')))
          → quot.eq (≈ (X ⟶ D)) (mk≈ k {p} {q} e')}})
          z
          z'

      ----------------------------------------------------------------
      -- Property (5.20)
      ----------------------------------------------------------------
      surjcan :
        (f : X → colim D)
        → -------------------------------------------------
        ∃ i ∶ Size , ∃ fi ∶ (X → vtx D i) , f == ν D i ∘ fi
      surjcan f with oldsklWISC (mkFam C F) (w a) f qD surjectionqD
      ... | ∃i c (∃i p (∃i f' (∧i surjp qDf'=fp))) =
        lemma (wAC (mkFam C' F') wiscB' (λ _ → Size) P Ptotal)
        where
        B' : Set l
        B' = set (x , y) ∶ (F c × F c), (p x == p y)

        wiscB' : wisc B' (mkFam C' F')
        wiscB' = w' ((c , a) , p)

        i : Size
        i = ⋁ˢ (in₁ c) (fst ∘ f')

        f'<ᵇi : {x : F c} → fst (f' x) <ᵇ i
        f'<ᵇi {x} = <ᵇ⋁ˢ (fst ∘ f') x

        fi : F c → vtx D i
        fi x = edg D i (fst (f' x)) {f'<ᵇi} (snd (f' x))

        νifi=fp : ν D i ∘ fi == f ∘ p
        νifi=fp = quot.funext λ x →
          proof
            ν D i (fi x)
          =[ symm (Coconeν D i (fst (f' x)) {f'<ᵇi} (snd (f' x))) ]
            ν D (fst (f' x)) (snd (f' x))
          =[ ap (case x) qDf'=fp ]
            f (p x)
          qed

        P : B' → Size → Prop l
        P ((x , y) ∣ _) j =
          ⋀ i<j ∶ (i < j),
            edg D j i {i<j} (fi x) ==
            edg D j i {i<j} (fi y)

        Ptotal : ∀ z → ∃ j ∶ Size , P z j
        Ptotal ((x , y) ∣ px=py) = h (quot-eff.prop (≈ D)
          (≈refl D)
          (≈symm D)
          (≈trans D)
          νifix=νifiy)
          where
          νifix=νifiy : ν D i (fi x) == ν D i (fi y)
          νifix=νifiy =
            proof
              ν D i (fi x)
            =[ ap (case x) νifi=fp ]
               f (p x)
            =[ ap f px=py ]
               f (p y)
            =[ symm (ap (case y) νifi=fp) ]
               ν D i (fi y)
            qed

          h :
            ≈ D (i , fi x) (i , fi y)
            → ----------------------------------
            ∃ j ∶ Size , ⋀ i<j ∶ (i < j),
              edg D j i {i<j} (fi x) ==
              edg D j i {i<j} (fi y)
          h (mk≈ k {p} e) = ∃i k (⋀i p e)

        lemma :
          (∃ c' ∶ C' ,
          ∃ p' ∶ (F' c' → B'),
          ∃ q' ∶ (F' c' → Size),
            (surjection p' ∧ ∀ z → P (p' z) (q' z)))
          → -------------------------------------------------
          ∃ i ∶ Size , ∃ fi ∶ (X → vtx D i) , f == ν D i ∘ fi
        lemma (∃i c' (∃i p' (∃i q' (∧i surjectionp' u)))) =
          ∃i j (∃i g f=νjg)
          where
          p₁ : F' c' → F c
          p₁ z' = fst (el (p' z'))

          p₂ : F' c' → F c
          p₂ z' = snd (el (p' z'))

          pp₁=pp₂ : ∀ z' → p (p₁ z') == p (p₂ z')
          pp₁=pp₂ z' = pf (p' z')

          b : Op Ψ
          b = in₂ c'

          j : Size
          j = i ∨ˢ ⋁ˢ b q'

          i<ᵇj : i <ᵇ j
          i<ᵇj = <ᵇ∨ˢl _

          q'<ᵇj : ∀ z' → q' z' <ᵇ j
          q'<ᵇj z' = <ᵇ<ᵇ (<ᵇ∨ˢr _) (<ᵇ⋁ˢ q' z')

          fj : F c → vtx D j
          fj z = edg D j i {i<ᵇj} (fi z)

          νjfj=fp : ∀ x → ν D j (fj x) == f (p x)
          νjfj=fp x =
            proof
              ν D j (fj x)
            =[ symm (Coconeν D j i {i<ᵇj} (fi x)) ]
               ν D i (fi x)
            =[ ap (case x) νifi=fp ]
               f (p x)
            qed

          fjp₁=fjp₂ : ∀ z' → fj (p₁ z') == fj (p₂ z')
          fjp₁=fjp₂ z' with u z' -- : P(p' z')(q' z')
          ... | ⋀i i<q'z' v =
            proof
              edg D j i {i<ᵇj} (fi (p₁ z'))
            =[ act D j (q' z') {q'<ᵇj z'} i {i<q'z'} _ ]
              edg D j (q' z') {q'<ᵇj z'}
                (edg D (q' z') i {i<q'z'} (fi (p₁ z')))
            =[ ap (edg D j (q' z') {q'<ᵇj z'}) v ]
              edg D j (q' z') {q'<ᵇj z'}
                (edg D (q' z') i {i<q'z'} (fi (p₂ z')))
            =[ symm (act D j (q' z') {q'<ᵇj z'} i {i<q'z'} _) ]
              edg D j i {i<ᵇj} (fi (p₂ z'))
            qed

          g : X → vtx D j
          g = EffEpi.lift p surjp {C = vtx D j} fj λ y y' e →
            match (surjectionp' ((y , y') ∣ e)) \ where
              (∃i z' refl) → fjp₁=fjp₂ z'

          f=νjg : f == ν D j ∘ g
          f=νjg = funext λ x → match (surjp x) \ where
            (∃i z refl) →
              proof
                f (p z)
              =[ symm (νjfj=fp z) ]
                ν D j (fj z)
              =[ ap (ν D j) (symm (EffEpi.comp p surjp {C = vtx D j} fj
                 (λ y y' e → match (surjectionp' ((y , y') ∣ e)) \ where
                   (∃i z' refl) → fjp₁=fjp₂ z') z)) ]
                ν D j (g (p z))
              qed

      ----------------------------------------------------------------
      -- Proof of part (3): surjectivity of the canonical function
      -- colim (X ⟶ D) → (X → colim D)
      ----------------------------------------------------------------
      surjectioncan : surjection (can X D)
      surjectioncan f = match (surjcan f) (λ{
        (∃i i (∃i fi refl))
          → ∃i ([ (i , fi) ]/ ≈ (X ⟶ D)) refl
        })

      isIsocan =
        bijectionIsIso (can (Ar Σ a) D)
          (∧i injectioncan surjectioncan)



----------------------------------------------------------------------
-- Cocontinuity of taking powers (Theorem 5.7)
----------------------------------------------------------------------
module CocontinuityOfTakingPowers
  {l : Level}
  (Σ : Sig {l})
  where
  open ConstructiveCocontinuity hiding (theorem)
  theorem :
    ∃ Size ∶ Set l ,
    ∃ ssz ∶ SizeStructure Size ,
      (let open Colim Size {{ssz}} in
        ((a : Op Σ)(D : Diag) → isIso (can (Ar Σ a) D)))
  theorem
    with IWISC (mkFam (Op Σ) (Ar Σ))
  ... | ∃i (mkFam C F) w
    with IWISC (mkFam (∑ (c , a) ∶ C × (Op Σ) , (F c → Ar Σ a)) λ{(_ , f) → ker f})
  ... | ∃i (mkFam C' F') w' = ConstructiveCocontinuity.theorem
    Σ (mkWISC-Cover C F w) (mkWISC-Cover C' F' w')
    
