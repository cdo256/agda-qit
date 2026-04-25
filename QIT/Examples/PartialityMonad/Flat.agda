module QIT.Examples.PartialityMonad.Flat where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)


record DirectAlgebra : Set₁ where
  infix 4 _≤_

  field
    A⊥ : Set
    _≤_ : A⊥ → A⊥ → Set

    η : Bool → A⊥
    ⊥ : A⊥
    ⨆ : (a : ℕ → A⊥) → (inc : ∀ i → a i ≤ a (suc i)) → A⊥
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a inc i → a i ≤ ⨆ a inc
    ⨆≤ : ∀ a inc x → (∀ i → a i ≤ x) → ⨆ a inc ≤ x
    antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y

record MutualAlgebra : Set₁ where
  field
    A⊥ : Set
    ≤∙ : Set

    ≤fst : ≤∙ → A⊥
    ≤snd : ≤∙ → A⊥
    η : Bool → A⊥
    ⊥ : A⊥
    ⨆ : (a : ℕ → A⊥)
      → (inc : ∀ i → ≤∙)
      → (inc-fst : ∀ i → ≤fst (inc i) ≡ a i)
      → (inc-snd : ∀ i → ≤snd (inc i) ≡ a (suc i))
      → A⊥
    ≤refl : (x : A⊥) → ≤∙
    ≤refl-fst : ∀ x → ≤fst (≤refl x) ≡ x
    ≤refl-snd : ∀ x → ≤snd (≤refl x) ≡ x
    ≤trans : ∀ x y z
           → (p q : ≤∙)
           → ≤fst p ≡ x → ≤snd p ≡ y
           → ≤fst q ≡ y → ≤snd q ≡ z
           → ≤∙
    ≤trans-fst : ∀ x y z p q p-fst p-snd q-fst q-snd
               → ≤fst (≤trans x y z p q p-fst p-snd q-fst q-snd) ≡ x
    ≤trans-snd : ∀ x y z p q p-fst p-snd q-fst q-snd
               → ≤snd (≤trans x y z p q p-fst p-snd q-fst q-snd) ≡ z
    ⊥≤ : (x : A⊥) → ≤∙
    ⊥≤-fst : ∀ x → ≤fst (⊥≤ x) ≡ ⊥
    ⊥≤-snd : ∀ x → ≤snd (⊥≤ x) ≡ x
    ≤⨆ : (a : ℕ → A⊥)
       → (inc : ∀ i → ≤∙)
       → (inc-fst : ∀ i → ≤fst (inc i) ≡ a i)
       → (inc-snd : ∀ i → ≤snd (inc i) ≡ a (suc i))
       → ℕ
       → ≤∙
    ≤⨆-fst : ∀ a inc inc-fst inc-snd i 
           → ≤fst (≤⨆ a inc inc-fst inc-snd i) ≡ a i
    ≤⨆-snd : ∀ a inc inc-fst inc-snd (i : ℕ) 
           → ≤snd (≤⨆ a inc inc-fst inc-snd i)
           ≡ ⨆ a inc inc-fst inc-snd
    ⨆≤ : (a : ℕ → A⊥)
       → (inc : ∀ i → ≤∙)
       → (inc-fst : ∀ i → ≤fst (inc i) ≡ a i)
       → (inc-snd : ∀ i → ≤snd (inc i) ≡ a (suc i))
       → (x : A⊥)
       → (ch≤ : ℕ → ≤∙)
       → (ch≤-fst : ∀ i → ≤fst (ch≤ i) ≡ a i)
       → (ch≤-snd : ∀ i → ≤snd (ch≤ i) ≡ x)
       → ≤∙
    ⨆≤-fst : ∀ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd
           → ≤fst (⨆≤ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd)
           ≡ ⨆ a inc inc-fst inc-snd
    ⨆≤-snd : ∀ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd
           → ≤snd (⨆≤ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd)
           ≡ x
    antisym : ∀ x y
            → (p q : ≤∙)
            → ≤fst p ≡ x → ≤snd p ≡ y
            → ≤fst q ≡ y → ≤snd q ≡ x
            → x ≡ y

record DirectAlgIso (A B : DirectAlgebra) : Set₁ where
  module A = DirectAlgebra A
  module B = DirectAlgebra B
  open A using () renaming (A⊥ to A₀)
  open B using () renaming (A⊥ to B₀)

  field
    f : A₀ → B₀
    g : B₀ → A₀

    fg : ∀ x → g (f x) ≡ x
    gf : ∀ y → f (g y) ≡ y

    η-pres : ∀ b → f (A.η b) ≡ B.η b
    ⊥-pres : f A.⊥ ≡ B.⊥

    ≤-pres : ∀ {x y} → x A.≤ y → f x B.≤ f y
    ≤-reflect : ∀ {x y} → f x B.≤ f y → x A.≤ y

    ⨆-pres :
      ∀ a inc →
      f (A.⨆ a inc)
      ≡
      B.⨆ (λ i → f (a i)) (λ i → ≤-pres (inc i))

record MutualAlgIso (A B : MutualAlgebra) : Set₁ where
  module A = MutualAlgebra A
  module B = MutualAlgebra B
  open A using () renaming (A⊥ to A₀)
  open B using () renaming (A⊥ to B₀)
  field
    f : A₀ → B₀
    g : B₀ → A₀

    edge-f : A.≤∙ → B.≤∙
    edge-g : B.≤∙ → A.≤∙

    edge-fst-pres :
      ∀ p → MutualAlgebra.≤fst B (edge-f p)
          ≡ f (MutualAlgebra.≤fst A p)

    edge-snd-pres :
      ∀ p → MutualAlgebra.≤snd B (edge-f p)
          ≡ f (MutualAlgebra.≤snd A p)

    -- plus operation preservation


module Iso where
  module D = DirectAlgebra
  module M = MutualAlgebra

  D→M : DirectAlgebra → MutualAlgebra
  D→M A = record
    { A⊥ = A⊥
    ; ≤∙ = Σ A⊥ λ x → Σ A⊥ λ y → x ≤ y
    ; ≤fst = λ (x , y , p) → x
    ; ≤snd = λ (x , y , p) → y
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
    where
    open DirectAlgebra A
    ≤∙ = Σ A⊥ λ x → Σ A⊥ λ y → x ≤ y
    ≤fst : ≤∙ → A⊥
    ≤fst = λ (x , y , p) → x
    ≤snd : ≤∙ → A⊥
    ≤snd = λ (x , y , p) → y
    ≤∙→≤ : ∀ {x y} → (p∙ : ≤∙)
         → ≤fst p∙ ≡ x → ≤snd p∙ ≡ y
         → x ≤ y
    ≤∙→≤ {x} {y} (x' , y' , p) x'≡x y'≡y =
      ≡.subst₂ _≤_ x'≡x y'≡y p

  M→D : MutualAlgebra → DirectAlgebra
  M→D A = record
    { A⊥ = A⊥
    ; _≤_ = _≤_
    ; η = η
    ; ⊥ = ⊥
    ; ⨆ = λ a inc → ⨆ a (λ i → fst (inc i))
        (λ i → ≤fst≡ (inc i)) λ i → ≤snd≡ (inc i)
    ; ≤refl = λ {x} → ≤refl x , ≤refl-fst x , ≤refl-snd x
    ; ≤trans = λ {x y z} p q
      → (≤trans x y z (fst p) (fst q)
                (≤fst≡ p) (≤snd≡ p)
                (≤fst≡ q) (≤snd≡ q)) , (≤trans-fst x y z (fst p) (fst q) (≤fst≡ p) (≤snd≡ p) (≤fst≡ q) (≤snd≡ q)) , ≤trans-snd x y z (fst p) (fst q) (≤fst≡ p) (≤snd≡ p) (≤fst≡ q) (≤snd≡ q)
    ; ⊥≤ = λ {x} → ⊥≤ x , ⊥≤-fst x , ⊥≤-snd x
    ; ≤⨆ = λ a inc i → ≤⨆ a (λ j → fst (inc j)) (λ j → ≤fst≡ (inc j))
         (λ j → ≤snd≡ (inc j)) i , (≤⨆-fst a (λ j → fst (inc j)) (λ j → ≤fst≡ (inc j)) (λ j → ≤snd≡ (inc j)) i) , ≤⨆-snd a (λ j → fst (inc j)) (λ j → ≤fst≡ (inc j)) (λ j → ≤snd≡ (inc j)) i
    ; ⨆≤ = λ a inc x p → (⨆≤ a (λ i → fst (inc i)) (λ i → ≤fst≡ (inc i)) (λ i → ≤snd≡ (inc i)) x (λ i → fst (p i)) (λ i → ≤fst≡ (p i)) λ i
           → ≤snd≡ (p i)) , (⨆≤-fst a (λ i → fst (inc i)) (λ i → _) (λ i → _) x
           (λ i → fst (p i)) (λ i → _) (λ i → _)) , (⨆≤-snd a (λ i → fst (inc i))
           (λ i → _) (λ i → _) x (λ i → fst (p i)) (λ i → _) (λ i → _))
    ; antisym = λ {x} {y} z z₁ →
                   antisym x y (z .fst) (z₁ .fst) (z .snd ._∧ᵖ_.fst)
                   (z .snd ._∧ᵖ_.snd) (z₁ .snd ._∧ᵖ_.fst) (z₁ .snd ._∧ᵖ_.snd)
    }
    where
    open MutualAlgebra A
    _≤_ : A⊥ → A⊥ → Set
    x ≤ y = ΣP ≤∙ λ p → (≤fst p ≡ x) ∧ (≤snd p ≡ y)
    ≤fst≡ : ∀ {x y} → (p : x ≤ y) → ≤fst (fst p) ≡ x
    ≤fst≡ {x} {y} (p , q , r) = q
    ≤snd≡ : ∀ {x y} → (p : x ≤ y) → ≤snd (fst p) ≡ y
    ≤snd≡ {x} {y} (p , q , r) = r



-- -- -- module Properties where
-- -- --   ≈proj1 : ∀ {x y} → x ≈ y → x ≤ y
-- -- --   ≈proj1 (≈antisym p q) = p
-- -- --   ≈proj2 : ∀ {x y} → x ≈ y → y ≤ x
-- -- --   ≈proj2 (≈antisym p q) = q

-- -- --   ≈refl : ∀ {x} → x ≈ x
-- -- --   ≈refl = ≈antisym ≤refl ≤refl
-- -- --   ≈sym : ∀ {x y} → x ≈ y → y ≈ x
-- -- --   ≈sym x≈y = ≈antisym y≤x x≤y
-- -- --     where
-- -- --     x≤y = ≈proj1 x≈y
-- -- --     y≤x = ≈proj2 x≈y
-- -- --   ≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
-- -- --   ≈trans x≈y y≈z = ≈antisym (≤trans x≤y y≤z) (≤trans z≤y y≤x)
-- -- --     where
-- -- --     x≤y = ≈proj1 x≈y
-- -- --     y≤x = ≈proj2 x≈y
-- -- --     y≤z = ≈proj1 y≈z
-- -- --     z≤y = ≈proj2 y≈z

-- -- --   ≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
-- -- --   ≤cong x≈x' y≈y' x≤y = ≤trans x'≤x (≤trans x≤y y≤y')
-- -- --     where
-- -- --     x≤x' = ≈proj1 x≈x'
-- -- --     x'≤x = ≈proj2 x≈x'
-- -- --     y≤y' = ≈proj1 y≈y'
-- -- --     y'≤y = ≈proj2 y≈y'

-- -- --   ≤cong⨆ : {a b : ℕ → A⊥}
-- -- --          → {inc : ∀ i → a i ≤ a (suc i)}
-- -- --          → {b-inc : ∀ i → b i ≤ b (suc i)}
-- -- --          → (p : ∀ i → a i ≤ b i)
-- -- --          → ⨆ a inc ≤ ⨆ b b-inc
-- -- --   ≤cong⨆ p =
-- -- --     ⨆≤ _ _ _ (λ i → ≤trans (p i) (≤⨆ _ _ i))

-- -- --   ≈cong⨆ : {a b : ℕ → A⊥}
-- -- --          → {inc : ∀ i → a i ≤ a (suc i)}
-- -- --          → {b-inc : ∀ i → b i ≤ b (suc i)}
-- -- --          → (p : ∀ i → a i ≈ b i)
-- -- --          → ⨆ a inc ≈ ⨆ b b-inc
-- -- --   ≈cong⨆ p =
-- -- --     ≈antisym (≤cong⨆ λ i → ≈proj1 (p i))
-- -- --              (≤cong⨆ λ i → ≈proj2 (p i))
