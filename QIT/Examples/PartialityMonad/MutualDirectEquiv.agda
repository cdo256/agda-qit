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
  ; antisym = λ {x} {y} z z₁
      → antisym x y (z .fst) (z₁ .fst)
                (z .snd ._∧ᵖ_.fst) (z .snd ._∧ᵖ_.snd)
                (z₁ .snd ._∧ᵖ_.fst) (z₁ .snd ._∧ᵖ_.snd)
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
equiv = record { F = F ; G = {!!} ; η = {!!} ; ε = {!!} }
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
    where
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
