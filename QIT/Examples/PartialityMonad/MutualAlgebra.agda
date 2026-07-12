open import QIT.Prelude

module QIT.Examples.PartialityMonad.MutualAlgebra ⦃ a!c* : A!C ⦄ ⦃ pathElim* : PathElim ⦄ where

open import QIT.Prelude
open import QIT.Prop hiding (⊥)
open import QIT.Relation.Subset
open import QIT.Relation.Nullary
open import QIT.Nat as ℕ

record Algebra : Set₁ where
  field
    A⊥ : Set
    ≤∙ : Set
    ≤fst : ≤∙ → A⊥
    ≤snd : ≤∙ → A⊥
    isProp≤ : ∀ p q
            → ≤fst p ≡ ≤fst q
            → ≤snd p ≡ ≤snd q
            → p ≡ q

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

open Algebra public

record Hom (A B : Algebra) : Set₁ where
  module A = Algebra A
  module B = Algebra B
  open A using () renaming (A⊥ to A₀; ≤∙ to ≤∙ᴬ)
  open B using () renaming (A⊥ to B₀; ≤∙ to ≤∙ᴮ)
  field
    f : A₀ → B₀
    f≤ : ≤∙ᴬ → ≤∙ᴮ

    f≤-fst : ∀ p → B.≤fst (f≤ p) ≡ f (A.≤fst p)
    f≤-snd : ∀ p → B.≤snd (f≤ p) ≡ f (A.≤snd p)

    η : ∀ b → f (A.η b) ≡ B.η b
    ⊥ : f A.⊥ ≡ B.⊥

    ⨆ : ∀ a inc inc-fst inc-snd
      → f (A.⨆ a inc inc-fst inc-snd)
      ≡ B.⨆ (λ i → f (a i))
            (λ i → f≤ (inc i))
            (λ i → ≡.trans (f≤-fst (inc i)) (≡.cong f (inc-fst i)))
            (λ i → ≡.trans (f≤-snd (inc i)) (≡.cong f (inc-snd i)))

    ≤refl : ∀ x
          → f≤ (A.≤refl x)
          ≡ B.≤refl (f x)

    ≤trans : ∀ x y z p q p-fst p-snd q-fst q-snd
           → f≤ (A.≤trans x y z p q p-fst p-snd q-fst q-snd)
           ≡ B.≤trans (f x) (f y) (f z)
                      (f≤ p) (f≤ q)
                      (≡.trans (f≤-fst p) (≡.cong f p-fst))
                      (≡.trans (f≤-snd p) (≡.cong f p-snd))
                      (≡.trans (f≤-fst q) (≡.cong f q-fst))
                      (≡.trans (f≤-snd q) (≡.cong f q-snd))

    ⊥≤ : ∀ x → f≤ (A.⊥≤ x) ≡ B.⊥≤ (f x)

    ≤⨆ : ∀ a inc inc-fst inc-snd i
       → f≤ (A.≤⨆ a inc inc-fst inc-snd i)
       ≡ B.≤⨆ (λ j → f (a j))
              (λ j → f≤ (inc j))
              (λ j → ≡.trans (f≤-fst (inc j)) (≡.cong f (inc-fst j)))
              (λ j → ≡.trans (f≤-snd (inc j)) (≡.cong f (inc-snd j)))
              i

    ⨆≤ : ∀ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd
       → f≤ (A.⨆≤ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd)
       ≡ B.⨆≤ (λ i → f (a i))
              (λ i → f≤ (inc i))
              (λ i → ≡.trans (f≤-fst (inc i)) (≡.cong f (inc-fst i)))
              (λ i → ≡.trans (f≤-snd (inc i)) (≡.cong f (inc-snd i)))
              (f x)
              (λ i → f≤ (ch≤ i))
              (λ i → ≡.trans (f≤-fst (ch≤ i)) (≡.cong f (ch≤-fst i)))
              (λ i → ≡.trans (f≤-snd (ch≤ i)) (≡.cong f (ch≤-snd i)))

id : ∀ {A} → Hom A A
id = record
  { f = λ z → z
  ; f≤ = λ p → p
  ; f≤-fst = λ _ → ≡.refl
  ; f≤-snd = λ _ → ≡.refl
  ; η = λ _ → ≡.refl
  ; ⊥ = ≡.refl
  ; ⨆ = λ _ _ _ _ → ≡.refl
  ; ≤refl = λ _ → ≡.refl
  ; ≤trans = λ _ _ _ _ _ _ _ _ _ → ≡.refl
  ; ⊥≤ = λ _ → ≡.refl
  ; ≤⨆ = λ _ _ _ _ _ → ≡.refl
  ; ⨆≤ = λ _ _ _ _ _ _ _ _ → ≡.refl
  }

_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ {A} {B} {C} g f = record
  { f = λ x → g₀ (f₀ x)
  ; f≤ = λ p → g.f≤ (f.f≤ p)
  ; f≤-fst = λ p →
      ≡.trans (g.f≤-fst (f.f≤ p))
              (≡.cong g₀ (f.f≤-fst p))
  ; f≤-snd = λ p →
      ≡.trans (g.f≤-snd (f.f≤ p))
              (≡.cong g₀ (f.f≤-snd p))
  ; η = λ b → ≡.trans (≡.cong g₀ (f.η b)) (g.η b)
  ; ⊥ = ≡.trans (≡.cong g₀ f.⊥) g.⊥
  ; ⨆ = λ a inc inc-fst inc-snd →
      ≡.trans (≡.cong g₀ (f.⨆ a inc inc-fst inc-snd))
              (g.⨆ (λ i → f₀ (a i))
                   (λ i → f.f≤ (inc i))
                   (λ i → ≡.trans (f.f≤-fst (inc i)) (≡.cong f₀ (inc-fst i)))
                   (λ i → ≡.trans (f.f≤-snd (inc i)) (≡.cong f₀ (inc-snd i))))
  ; ≤refl = λ x →
      ≡.trans (≡.cong g.f≤ (f.≤refl x))
              (g.≤refl (f₀ x))
  ; ≤trans = λ x y z p q p-fst p-snd q-fst q-snd →
      ≡.trans (≡.cong g.f≤ (f.≤trans x y z p q p-fst p-snd q-fst q-snd))
              (g.≤trans (f₀ x) (f₀ y) (f₀ z)
                        (f.f≤ p) (f.f≤ q)
                        (≡.trans (f.f≤-fst p) (≡.cong f₀ p-fst))
                        (≡.trans (f.f≤-snd p) (≡.cong f₀ p-snd))
                        (≡.trans (f.f≤-fst q) (≡.cong f₀ q-fst))
                        (≡.trans (f.f≤-snd q) (≡.cong f₀ q-snd)))
  ; ⊥≤ = λ x →
      ≡.trans (≡.cong g.f≤ (f.⊥≤ x))
              (g.⊥≤ (f₀ x))
  ; ≤⨆ = λ a inc inc-fst inc-snd i →
      ≡.trans (≡.cong g.f≤ (f.≤⨆ a inc inc-fst inc-snd i))
              (g.≤⨆ (λ j → f₀ (a j))
                    (λ j → f.f≤ (inc j))
                    (λ j → ≡.trans (f.f≤-fst (inc j)) (≡.cong f₀ (inc-fst j)))
                    (λ j → ≡.trans (f.f≤-snd (inc j)) (≡.cong f₀ (inc-snd j)))
                    i)
  ; ⨆≤ = λ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd →
      ≡.trans (≡.cong g.f≤ (f.⨆≤ a inc inc-fst inc-snd x ch≤ ch≤-fst ch≤-snd))
              (g.⨆≤ (λ i → f₀ (a i))
                    (λ i → f.f≤ (inc i))
                    (λ i → ≡.trans (f.f≤-fst (inc i)) (≡.cong f₀ (inc-fst i)))
                    (λ i → ≡.trans (f.f≤-snd (inc i)) (≡.cong f₀ (inc-snd i)))
                    (f₀ x)
                    (λ i → f.f≤ (ch≤ i))
                    (λ i → ≡.trans (f.f≤-fst (ch≤ i)) (≡.cong f₀ (ch≤-fst i)))
                    (λ i → ≡.trans (f.f≤-snd (ch≤ i)) (≡.cong f₀ (ch≤-snd i))))
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  open A using () renaming (A⊥ to A₀)
  open B using () renaming (A⊥ to B₀)
  open C using () renaming (A⊥ to C₀)
  module f = Hom f
  module g = Hom g
  open f renaming (f to f₀)
  open g renaming (f to g₀)

open import QIT.Relation.Binary
open import QIT.Category.Base

record _≈_ {A B} (f g : Hom A B) : Prop ℓ0 where
  constructor mk≈
  module f = Hom f
  module g = Hom g
  field
    f≡ : ∀ a → f.f a ≡ g.f a
    f≤≡ : ∀ p → f.f≤ p ≡ g.f≤ p

isEquiv≈ : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
isEquiv≈ = record
  { refl = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; sym = λ (mk≈ p q) → mk≈ (λ a → ≡.sym (p a)) (λ p' → ≡.sym (q p'))
  ; trans = λ (mk≈ p q) (mk≈ r s)
          → mk≈ (λ a → ≡.trans (p a) (r a))
                (λ p' → ≡.trans (q p') (s p'))
  }

∘-resp-≈ : ∀ {A B C} {f h : Hom B C} {g i : Hom A B}
         → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} (mk≈ p q) (mk≈ r s) =
  mk≈ (λ a → ≡.trans (≡.cong (Hom.f f) (r a)) (p (Hom.f i a)))
      (λ p' → ≡.trans (≡.cong (Hom.f≤ f) (s p')) (q (Hom.f≤ i p')))

Cat : Category (lsuc ℓ0) (lsuc ℓ0) ℓ0
Cat = record
  { Obj = Algebra
  ; _⇒_ = Hom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; sym-assoc = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; identityˡ = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; identityʳ = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; identity² = mk≈ (λ _ → ≡.refl) (λ _ → ≡.refl)
  ; equiv = isEquiv≈
  ; ∘-resp-≈ = ∘-resp-≈
  }
