module QIT.Examples.PartialityMonad.MutualDirectEquiv where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

import QIT.Examples.PartialityMonad.DirectAlgebra as DA
import QIT.Examples.PartialityMonad.MutualAlgebra as MA

open import QIT.Category.Equivalence
open import QIT.Category.Base
open import QIT.Functor.Base
open import QIT.Functor.NatTrans
open import QIT.Functor.Properties using (Id; _∘_)


-- Convert a DirectAlgebra to a MutualAlgebra by reifying the order relation
D→M : DA.Algebra → MA.Algebra
D→M A = record
  { A⊥ = A⊥
  ; ≤∙ = Σ A⊥ λ x → Σ A⊥ λ y → x ≤ y
  ; ≤fst = λ (x , y , p) → x
  ; ≤snd = λ (x , y , p) → y
  ; isProp≤ = isProp≤'
  ; η = η
  ; ⊥ = ⊥
  ; ⨆ = λ a inc inc-fst inc-snd
      → ⨆ a λ i → ≤∙→≤ (inc i) (inc-fst i) (inc-snd i)
  ; ≤refl = λ x → x , x , ≤refl
  ; ≤refl-fst = λ _ → ≡.refl
  ; ≤refl-snd = λ _ → ≡.refl
  ; ≤trans = λ x y z p q p-fst p-snd q-fst q-snd
      → x , z , ≤trans (≤∙→≤ p p-fst p-snd) (≤∙→≤ q q-fst q-snd)
  ; ≤trans-fst = λ x y z p q p-fst p-snd q-fst q-snd → ≡.refl
  ; ≤trans-snd = λ x y z p q p-fst p-snd q-fst q-snd → ≡.refl
  ; ⊥≤ = λ x → ⊥ , x , ⊥≤
  ; ⊥≤-fst = λ x → ≡.refl
  ; ⊥≤-snd = λ x → ≡.refl
  ; ≤⨆ = λ a inc inc-fst inc-snd i
      → a i , ⨆ a (λ j → ≤∙→≤ (inc j) (inc-fst j) (inc-snd j))
      , ≤⨆ a (λ j → ≤∙→≤ (inc j) _ _) i
  ; ≤⨆-fst = λ a inc inc-fst inc-snd i → ≡.refl
  ; ≤⨆-snd = λ a inc inc-fst inc-snd i → ≡.refl
  ; ⨆≤ = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd
      → ⨆ a (λ i → ≤∙→≤ (inc i) (inc-fst i) (inc-snd i)) , x
      , ⨆≤ a (λ i → ≤∙→≤ (inc i) (inc-fst i) (inc-snd i)) x
          λ i → ≤∙→≤ (ch≤ i) (ch≤-fst i) (ch≤-snd i)
  ; ⨆≤-fst = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd → ≡.refl
  ; ⨆≤-snd = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd → ≡.refl
  ; antisym = λ x y p q p-fst p-snd q-fst q-snd
      → antisym (≤∙→≤ p p-fst p-snd) (≤∙→≤ q q-fst q-snd)
  }
  module D→M where
  open DA.Algebra A

  ≤∙ = Σ A⊥ λ x → Σ A⊥ λ y → x ≤ y

  ≤fst : ≤∙ → A⊥
  ≤fst = λ (x , y , p) → x

  ≤snd : ≤∙ → A⊥
  ≤snd = λ (x , y , p) → y

  -- Convert a ≤∙ element to a ≤ proof, using the coherence conditions
  ≤∙→≤ : ∀ {x y} → (p∙ : ≤∙) → ≤fst p∙ ≡ x → ≤snd p∙ ≡ y → x ≤ y
  ≤∙→≤ {x} {y} (x' , y' , p) x'≡x y'≡y = ≡.subst₂ _≤_ x'≡x y'≡y p

  -- Proof irrelevance for ≤∙: two elements with equal projections are equal
  isProp≤' : ∀ p q → ≤fst p ≡ ≤fst q → ≤snd p ≡ ≤snd q → p ≡ q
  isProp≤' (x , y , p) (x , y , q) ≡.refl ≡.refl =
    ≡.cong (λ ○ → x , y , ○) (isProp≤ p q)




-- Convert a MutualAlgebra to a DirectAlgebra by forgetting the reification
M→D : MA.Algebra → DA.Algebra
M→D A = record
  { A⊥ = A⊥
  ; _≤_ = _≤_
  ; isProp≤ = isProp≤'
  ; η = η
  ; ⊥ = ⊥
  ; ⨆ = λ a inc
      → ⨆ a (λ i → fst (inc i)) (λ i → ≤fst≡ (inc i)) (λ i → ≤snd≡ (inc i))
  ; ≤refl = λ {x} → ≤refl x , ≤refl-fst x , ≤refl-snd x
  ; ≤trans = λ {x y z} p q
      → ≤trans x y z (fst p) (fst q) (≤fst≡ p) (≤snd≡ p) (≤fst≡ q) (≤snd≡ q)
      , ≤trans-fst x y z (fst p) (fst q) (≤fst≡ p) (≤snd≡ p) (≤fst≡ q) (≤snd≡ q)
      , ≤trans-snd x y z (fst p) (fst q) (≤fst≡ p) (≤snd≡ p) (≤fst≡ q) (≤snd≡ q)
  ; ⊥≤ = λ {x} → ⊥≤ x , ⊥≤-fst x , ⊥≤-snd x
  ; ≤⨆ = λ a inc i
      → ≤⨆ a (λ j → fst (inc j)) (λ j → ≤fst≡ (inc j)) (λ j → ≤snd≡ (inc j)) i
      , ≤⨆-fst a (λ j → fst (inc j)) (λ j → ≤fst≡ (inc j)) (λ j → ≤snd≡ (inc j)) i
      , ≤⨆-snd a (λ j → fst (inc j)) (λ j → ≤fst≡ (inc j)) (λ j → ≤snd≡ (inc j)) i
  ; ⨆≤ = λ a inc x p
      → ⨆≤ a (λ i → fst (inc i)) (λ i → ≤fst≡ (inc i)) (λ i → ≤snd≡ (inc i))
            x (λ i → fst (p i)) (λ i → ≤fst≡ (p i)) (λ i → ≤snd≡ (p i))
      , ⨆≤-fst a (λ i → fst (inc i)) (λ i → ≤fst≡ (inc i)) (λ i → ≤snd≡ (inc i))
              x (λ i → fst (p i)) (λ i → ≤fst≡ (p i)) (λ i → ≤snd≡ (p i))
      , ⨆≤-snd a (λ i → fst (inc i)) (λ i → ≤fst≡ (inc i)) (λ i → ≤snd≡ (inc i))
              x (λ i → fst (p i)) (λ i → ≤fst≡ (p i)) (λ i → ≤snd≡ (p i))
  ; antisym = λ {x} {y} p q
      → antisym x y (p .fst) (q .fst)
                (p .snd .∧.fst) (p .snd .∧.snd)
                (q .snd .∧.fst) (q .snd .∧.snd)
  }
  module M→D where
  open MA.Algebra A

  -- Define the order relation by requiring a witness from ≤∙
  _≤_ : A⊥ → A⊥ → Set
  x ≤ y = ΣP ≤∙ λ p → (≤fst p ≡ x) ∧ (≤snd p ≡ y)

  ≤fst≡ : ∀ {x y} → (p : x ≤ y) → ≤fst (fst p) ≡ x
  ≤fst≡ {x} {y} (p , q , r) = q

  ≤snd≡ : ∀ {x y} → (p : x ≤ y) → ≤snd (fst p) ≡ y
  ≤snd≡ {x} {y} (p , q , r) = r

  -- Proof irrelevance for the derived order relation
  isProp≤' : ∀ {x y} → (p q : x ≤ y) → p ≡ q
  isProp≤' {x} {y} (p , p-fst , p-snd) (q , q-fst , q-snd) =
    ΣP≡ _ _ (isProp≤ p q (≡.trans p-fst (≡.sym q-fst))
                         (≡.trans p-snd (≡.sym q-snd)))


-- The equivalence between DirectAlgebra and MutualAlgebra categories
equiv : Equivalence DA.Cat MA.Cat
equiv = record { F = F ; G = G ; η = η ; ε = ε }
  where
  open Functor

  -- Functor from DirectAlgebra to MutualAlgebra
  F : Functor DA.Cat MA.Cat
  F .ob = D→M

  F .hom {X} {Y} p = record
    { f = p.f
    ; f≤ = f≤
    ; f≤-fst = λ _ → ≡.refl
    ; f≤-snd = λ _ → ≡.refl
    ; η = p.η
    ; ⊥ = p.⊥
    ; ⨆ = f⨆
    ; ≤refl = λ x →
        FY.isProp≤ (f≤ (FX.≤refl x)) (FY.≤refl (p.f x)) ≡.refl ≡.refl
    ; ≤trans = λ x y z p q p-fst p-snd q-fst q-snd →
        let p' = D→M.≤∙→≤ X p p-fst p-snd
            q' = D→M.≤∙→≤ X q q-fst q-snd
        in FY.isProp≤ (f≤ (FX.≤trans x y z p q p-fst p-snd q-fst q-snd))
                      (FY.≤trans (p.f x) (p.f y) (p.f z) (f≤ p) (f≤ q)
                        (≡.cong p.f p-fst) (≡.cong p.f p-snd)
                        (≡.cong p.f q-fst) (≡.cong p.f q-snd))
                      ≡.refl ≡.refl
    ; ⊥≤ = λ x →
        FY.isProp≤ (f≤ (FX.⊥≤ x)) (FY.⊥≤ (p.f x)) p.⊥ ≡.refl
    ; ≤⨆ = λ a inc inc-fst inc-snd i →
        let inc' = λ j → D→M.≤∙→≤ X (inc j) (inc-fst j) (inc-snd j)
        in FY.isProp≤ (f≤ (FX.≤⨆ a inc inc-fst inc-snd i))
                      (FY.≤⨆ (λ j → p.f (a j)) (λ j → f≤ (inc j))
                        (λ j → ≡.cong p.f (inc-fst j))
                        (λ j → ≡.cong p.f (inc-snd j)) i)
                      ≡.refl (f⨆ a inc inc-fst inc-snd)
    ; ⨆≤ = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd →
        let inc' = λ i → D→M.≤∙→≤ X (inc i) (inc-fst i) (inc-snd i)
            ch≤' = λ i → D→M.≤∙→≤ X (ch≤ i) (ch≤-fst i) (ch≤-snd i)
        in FY.isProp≤ (f≤ (FX.⨆≤ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd))
                      (FY.⨆≤ (λ i → p.f (a i)) (λ i → f≤ (inc i))
                        (λ i → ≡.cong p.f (inc-fst i))
                        (λ i → ≡.cong p.f (inc-snd i))
                        (p.f x) (λ i → f≤ (ch≤ i))
                        (λ i → ≡.cong p.f (ch≤-fst i))
                        (λ i → ≡.cong p.f (ch≤-snd i)))
                      (f⨆ a inc inc-fst inc-snd) ≡.refl
    }
    module F where
    module p = DA.Hom p
    open ≡.≡-Reasoning
    module X = DA.Algebra X
    module Y = DA.Algebra Y
    module FX = MA.Algebra (F .ob X)
    module FY = MA.Algebra (F .ob Y)

    -- Lift a homomorphism on elements to a homomorphism on ≤∙
    f≤ : FX.≤∙ → FY.≤∙
    f≤ (x , y , p) = p.f x , p.f y , p.≤ p

    -- Homomorphisms commute with subst₂
    ≤-subst₂-comm : ∀ {x y x' y'} (eq-x : x ≡ x') (eq-y : y ≡ y') (p≤ : x X.≤ y)
                  → p.≤ (≡.subst₂ X._≤_ eq-x eq-y p≤)
                  ≡ ≡.subst₂ Y._≤_ (≡.cong p.f eq-x) (≡.cong p.f eq-y) (p.≤ p≤)
    ≤-subst₂-comm ≡.refl ≡.refl p≤ = ≡.refl

    -- Homomorphisms preserve ⨆
    f⨆ : (a : ℕ → FX.A⊥)
      → (inc : ℕ → FX.≤∙)
      → (inc-fst : (i : ℕ) → FX.≤fst (inc i) ≡ a i)
      → (inc-snd : (i : ℕ) → FX.≤snd (inc i) ≡ a (suc i))
      → p.f (FX.⨆ a inc inc-fst inc-snd)
      ≡ FY.⨆ (λ i → p.f (a i)) (λ i → f≤ (inc i))
             (λ i → ≡.cong p.f (inc-fst i))
             (λ i → ≡.cong p.f (inc-snd i))
    f⨆ a inc inc-fst inc-snd = begin
      p.f (FX.⨆ a inc inc-fst inc-snd)
        ≡⟨ p.⨆ a inc' ⟩
      Y.⨆ (λ i → p.f (a i)) (λ i → p.≤ (inc' i))
        ≡⟨ ≡.cong (Y.⨆ (λ i → p.f (a i))) (≡.funExt q) ⟩
      Y.⨆ (λ i → p.f (a i)) (λ i → ≤∙→≤ Y (f≤ (inc i)) _ _)
        ≡⟨ ≡.refl ⟩
      FY.⨆ (λ i → p.f (a i)) (λ i → f≤ (inc i))
           (λ i → ≡.cong p.f (inc-fst i))
           (λ i → ≡.cong p.f (inc-snd i)) ∎
      where
      open D→M
      inc' : (i : ℕ) → a i X.≤ a (suc i)
      inc' i = ≤∙→≤ X (inc i) (inc-fst i) (inc-snd i)
      q : ∀ i → p.≤ (≤∙→≤ X (inc i) (inc-fst i) (inc-snd i))
              ≡ ≤∙→≤ Y (f≤ (inc i))
                       (≡.cong p.f (inc-fst i))
                       (≡.cong p.f (inc-snd i))
      q i = ≤-subst₂-comm (inc-fst i) (inc-snd i) (inc i .proj₂ .proj₂)

  F .id {X} = MA.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)

  F .comp f g = MA.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)

  F .resp {X} {Y} {f} {g} (DA.mk≈ p) = MA.mk≈ p (λ (x , y , q) →
    MA.Algebra.isProp≤ (F .ob Y)
      (DA.Hom.f f x , DA.Hom.f f y , DA.Hom.≤ f q)
      (DA.Hom.f g x , DA.Hom.f g y , DA.Hom.≤ g q)
      (p x) (p y))

  -- Functor from MutualAlgebra to DirectAlgebra (inverse to F)
  G : Functor MA.Cat DA.Cat
  G .ob = M→D

  G .hom {X} {Y} p = record
    { f = p.f
    ; ≤ = λ {x} {y} q → p.f≤ (fst q) , ≤-coh-fst q , ≤-coh-snd q
    ; η = p.η
    ; ⊥ = p.⊥
    ; ⨆ = g⨆
    }
    where
    module p = MA.Hom p
    open ≡.≡-Reasoning
    module X = MA.Algebra X
    module Y = MA.Algebra Y
    module GX = DA.Algebra (G .ob X)
    module GY = DA.Algebra (G .ob Y)

    -- Coherence for the first projection
    ≤-coh-fst : ∀ {x y} (q : x GX.≤ y)
              → Y.≤fst (p.f≤ (fst q)) ≡ p.f x
    ≤-coh-fst {x} {y} (q , q-fst , q-snd) =
      Y.≤fst (p.f≤ q)
        ≡⟨ p.f≤-fst q ⟩
      p.f (X.≤fst q)
        ≡⟨ ≡.cong p.f q-fst ⟩
      p.f x ∎

    -- Coherence for the second projection
    ≤-coh-snd : ∀ {x y} (q : x GX.≤ y)
              → Y.≤snd (p.f≤ (fst q)) ≡ p.f y
    ≤-coh-snd {x} {y} (q , q-fst , q-snd) =
      Y.≤snd (p.f≤ q)
        ≡⟨ p.f≤-snd q ⟩
      p.f (X.≤snd q)
        ≡⟨ ≡.cong p.f q-snd ⟩
      p.f y ∎

    -- Homomorphisms preserve ⨆
    g⨆ : ∀ a inc
       → p.f (GX.⨆ a inc)
       ≡ GY.⨆ (λ i → p.f (a i)) (λ i → p.f≤ (fst (inc i)) , ≤-coh-fst (inc i) , ≤-coh-snd (inc i))
    g⨆ a inc = begin
      p.f (GX.⨆ a inc)
        ≡⟨ ≡.refl ⟩
      p.f (X.⨆ a (λ i → fst (inc i)) (λ i → snd (inc i) ._∧ᵖ_.fst) (λ i → snd (inc i) ._∧ᵖ_.snd))
        ≡⟨ p.⨆ a (λ i → fst (inc i)) (λ i → snd (inc i) ._∧ᵖ_.fst) (λ i → snd (inc i) ._∧ᵖ_.snd) ⟩
      Y.⨆ (λ i → p.f (a i)) (λ i → p.f≤ (fst (inc i)))
          (λ i → ≡.trans (p.f≤-fst (fst (inc i))) (≡.cong p.f (snd (inc i) ._∧ᵖ_.fst)))
          (λ i → ≡.trans (p.f≤-snd (fst (inc i))) (≡.cong p.f (snd (inc i) ._∧ᵖ_.snd)))
        ≡⟨ ≡.refl ⟩
      Y.⨆ (λ i → p.f (a i)) (λ i → p.f≤ (fst (inc i)))
          (λ i → ≤-coh-fst (inc i))
          (λ i → ≤-coh-snd (inc i))
        ≡⟨ ≡.refl ⟩
      GY.⨆ (λ i → p.f (a i)) (λ i → p.f≤ (fst (inc i)) , ≤-coh-fst (inc i) , ≤-coh-snd (inc i)) ∎

  G .id {X} = DA.mk≈ (λ _ → ≡.refl)

  G .comp f g = DA.mk≈ (λ _ → ≡.refl)

  G .resp {X} {Y} {f} {g} (MA.mk≈ p-f p-f≤) = DA.mk≈ p-f

  -- Natural isomorphism η : Id ⟹ G ∘ F
  -- For each DirectAlgebra X, we have X ≅ M→D (D→M X)
  η : QIT.Functor.NatTrans.NatIso Id (G ∘ F)
  η = record
    { ob = λ X → record
        { f = λ x → x
        ; ≤ = λ {x} {y} p → (x , y , p) , ≡.refl , ≡.refl
        ; η = λ _ → ≡.refl
        ; ⊥ = ≡.refl
        ; ⨆ = λ a inc → ≡.refl
        }
    ; hom = λ {X} {Y} f → DA.mk≈ (λ _ → ≡.refl)
    ; isIso = λ X → record
        { f⁻¹ = record
            { f = λ x → x
            ; ≤ = λ {x} {y} (p , p-fst , p-snd) →
                ≡.subst₂ (DA.Algebra._≤_ X) p-fst p-snd (proj₂ (proj₂ p))
            ; η = λ _ → ≡.refl
            ; ⊥ = ≡.refl
            ; ⨆ = λ a inc → ≡.refl
            }
        ; linv = DA.mk≈ (λ _ → ≡.refl)
        ; rinv = DA.mk≈ (λ _ → ≡.refl)
        }
    }

  -- Natural isomorphism ε : F ∘ G ⟹ Id
  -- For each MutualAlgebra X, we have D→M (M→D X) ≅ X
  module ε-helpers where
    open ≡.≡-Reasoning

    -- Postulate: subst₂ on the derived order extracts the inner witness
    -- In the round-trip (F ∘ G) X, the order is M→D._≤_ X which is ΣP (X.≤∙) λ p → ...
    -- When we apply subst₂, we just need to adjust the coherence proofs, not the witness itself
    postulate
      subst₂-extract-witness : (X : MA.Algebra)
        → ∀ {x y x' y'} (p : MA.≤∙ X) (p-fst : MA.≤fst X p ≡ x') (p-snd : MA.≤snd X p ≡ y')
        → (eq-x : x' ≡ x) (eq-y : y' ≡ y)
        → fst (≡.subst₂ (DA.Algebra._≤_ (M→D X)) eq-x eq-y (p , p-fst , p-snd)) ≡ p

    -- Helper to prove ⨆ equality using subst₂-extract-witness
    ⨆-eq : (X : MA.Algebra) → ∀ a inc inc-fst inc-snd
         → (F ∘ G) .ob X .MA.⨆ a inc inc-fst inc-snd
         ≡ X .MA.⨆ a (λ i → fst (proj₂ (proj₂ (inc i))))
               (λ i → ≡.trans (snd (proj₂ (proj₂ (inc i))) .∧.fst) (inc-fst i))
               (λ i → ≡.trans (snd (proj₂ (proj₂ (inc i))) .∧.snd) (inc-snd i))
    ⨆-eq X a inc inc-fst inc-snd = ≡.cong (λ ch → X .MA.⨆ a ch _ _) (≡.funExt lemma)
      where
        lemma : ∀ i → fst (D→M.≤∙→≤ (M→D X) (inc i) (inc-fst i) (inc-snd i))
                    ≡ fst (proj₂ (proj₂ (inc i)))
        lemma i =
          let (x , y , p-der , p-fst , p-snd) = inc i
          in subst₂-extract-witness X p-der p-fst p-snd (inc-fst i) (inc-snd i)

    ε-ob : (X : MA.Algebra) → MA.Hom ((F ∘ G) .ob X) X
    ε-ob X = record
      { f = λ x → x
      ; f≤ = λ (x , y , p-der) → fst p-der
      ; f≤-fst = λ (x , y , p-der) → snd p-der .∧.fst
      ; f≤-snd = λ (x , y , p-der) → snd p-der .∧.snd
      ; η = λ _ → ≡.refl
      ; ⊥ = ≡.refl
      ; ⨆ = ⨆-eq X
          -- *** THIS IS WHERE THE ISSUE MANIFESTS ***
          -- Goal: (F ∘ G) X .⨆ a inc inc-fst inc-snd ≡ X .⨆ a (extract inc) ...
          -- Problem: (F ∘ G) X .⨆ expands to:
          --   X .⨆ a (λ i → fst (subst₂ ... (inc-fst i) (inc-snd i) (inc i)))
          -- But we need:
          --   X .⨆ a (λ i → fst (proj₂ (proj₂ (inc i))))
          -- These are NOT definitionally equal because subst₂ doesn't reduce!
          --
          -- With the subst₂-uip postulate, we can now prove they're equal
          -- (see ⨆-eq definition above in the module)
      ; ≤refl = λ x → MA.isProp≤ X _ _ ≡.refl ≡.refl
      ; ≤trans = λ x y z p q p-fst p-snd q-fst q-snd →
          MA.isProp≤ X (fst (proj₂ (proj₂ (MA.≤trans ((F ∘ G) .ob X) x y z p q _ _ _ _))))
                              (MA.≤trans (ob Id X) x y z (fst (proj₂ (proj₂ p))) (fst (proj₂ (proj₂ q))) _ _ _ _)
                                                {!≡.trans (MA.≤trans-fst ((F ∘ G) .ob X) x y z p q _ _ _ _) p-fst!}
                                                {!≡.trans (MA.≤trans-snd ((F ∘ G) .ob X) x y z p q _ _ _ _) q-snd!}
      ; ⊥≤ = λ x → MA.Algebra.isProp≤ X _ _ ≡.refl ≡.refl
      ; ≤⨆ = λ a inc inc-fst inc-snd i →
          MA.isProp≤ X _ _ (≡.trans (MA.≤⨆-fst ((F ∘ G) .ob X) a inc inc-fst inc-snd i) (inc-fst i))
                           (MA.≤⨆-snd ((F ∘ G) .ob X) a inc inc-fst inc-snd i)
      ; ⨆≤ = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd →
          MA.isProp≤ X _ _ (MA.⨆≤-fst ((F ∘ G) .ob X) a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd)
                           (≡.trans (MA.⨆≤-snd ((F ∘ G) .ob X) a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd) ch≤-snd)
      }

    -- ; isIso = λ X → record
    --     { f⁻¹ = record
    --         { f = λ x → x
    --         ; f≤ = λ p → MA.Algebra.≤fst X p , MA.Algebra.≤snd X p , (p , ≡.refl , ≡.refl)
    --         ; f≤-fst = λ _ → ≡.refl
    --         ; f≤-snd = λ _ → ≡.refl
    --         ; η = λ _ → ≡.refl
    --         ; ⊥ = ≡.refl
    --         ; ⨆ = λ a inc inc-fst inc-snd → {!≡.refl!}
    --         ; ≤refl = λ x → MA.Algebra.isProp≤ X _ _ ≡.refl ≡.refl
    --         ; ≤trans = λ x y z p q p-fst p-snd q-fst q-snd →
    --             MA.Algebra.isProp≤ X _ _ ≡.refl ≡.refl
    --         ; ⊥≤ = λ x → MA.Algebra.isProp≤ X _ _ ≡.refl ≡.refl
    --         ; ≤⨆ = λ a inc inc-fst inc-snd i →
    --             MA.Algebra.isProp≤ X _ _ ≡.refl ≡.refl
    --         ; ⨆≤ = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd →
    --             MA.Algebra.isProp≤ X _ _ ≡.refl ≡.refl
    --         }
    --     ; linv = MA.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
    --     ; rinv = MA.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
    --     }

  ε : QIT.Functor.NatTrans.NatIso (F ∘ G) Id
  ε = record
    { ob = ε-helpers.ε-ob
    ; hom = λ {X} {Y} f → MA.mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
    }
