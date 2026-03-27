module QIT.Examples.PartialityMonad.Direct where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

interleaved mutual
  infix 4 _≤_ _≈_
  data Seq : Set
  data A⊥ : Set
  data _≤_ : A⊥ → A⊥ → Set
  data _≈_ : A⊥ → A⊥ → Set

  data _ where
    η : Bool → A⊥
    ⊥ : A⊥
    ⨆ : (a : Seq) → A⊥
    ⟦_⟧ : Seq → ℕ → A⊥
    _,_ : (f : ℕ → A⊥) → ((i : ℕ) → f i ≤ f (suc i)) → Seq
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a i → ⟦ a ⟧ i ≤ ⨆ a
    ⨆≤ : ∀ a x → (∀ i → ⟦ a ⟧ i ≤ x) → ⨆ a ≤ x
    inc : (a : Seq) → ∀ i → ⟦ a ⟧ i ≤ ⟦ a ⟧ (suc i)
    ≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y
    η,⟦⟧ : ∀ f f≤ i → ⟦ f , f≤ ⟧ i ≈ f i
    ≈sym : ∀ {x y} → x ≈ y → y ≈ x
    ≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
    ≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
    ≈→≤ : ∀ {x y} → x ≈ y → x ≤ y
    

record Algebra : Set₁ where
  infix 4 _≤ᴬ_ _≈ᴬ_

  field
    Seqᴬ : Set
    A⊥ᴬ : Set
    _≤ᴬ_ : A⊥ᴬ → A⊥ᴬ → Set
    _≈ᴬ_ : A⊥ᴬ → A⊥ᴬ → Set

    ηᴬ : Bool → A⊥ᴬ
    ⊥ᴬ : A⊥ᴬ
    ⨆ᴬ : Seqᴬ → A⊥ᴬ
    ⟦_⟧ᴬ : Seqᴬ → ℕ → A⊥ᴬ
    _,ᴬ_ : (f : ℕ → A⊥ᴬ)
         → ((i : ℕ) → f i ≤ᴬ f (suc i))
         → Seqᴬ

    ≤reflᴬ : ∀ {x} → x ≤ᴬ x
    ≤transᴬ : ∀ {x y z} → x ≤ᴬ y → y ≤ᴬ z → x ≤ᴬ z
    ⊥≤ᴬ : ∀ {x} → ⊥ᴬ ≤ᴬ x
    ≤⨆ᴬ : ∀ a i → ⟦ a ⟧ᴬ i ≤ᴬ ⨆ᴬ a
    ⨆≤ᴬ : ∀ a x → (∀ i → ⟦ a ⟧ᴬ i ≤ᴬ x) → ⨆ᴬ a ≤ᴬ x
    incᴬ : (a : Seqᴬ) → ∀ i → ⟦ a ⟧ᴬ i ≤ᴬ ⟦ a ⟧ᴬ (suc i)
    ≈antisymᴬ : ∀ {x y} → x ≤ᴬ y → y ≤ᴬ x → x ≈ᴬ y
    --TODO η,⟦⟧ : ∀ f f≤ i → ⟦ f , f≤ ⟧ i ≈ f i

record Rec (A : Algebra) : Set₁ where
  open Algebra A

  field
    Seqᴿ : Seq → Seqᴬ
    A⊥ᴿ  : A⊥ → A⊥ᴬ
    ≤ᴿ   : ∀ {x y} → x ≤ y → A⊥ᴿ x ≤ᴬ A⊥ᴿ y
    ≈ᴿ   : ∀ {x y} → x ≈ y → A⊥ᴿ x ≈ᴬ A⊥ᴿ y
    ηᴿ : ∀ b →
      A⊥ᴿ (η b) ≡ ηᴬ b
    ⊥ᴿ :
      A⊥ᴿ ⊥ ≡ ⊥ᴬ
    ⨆ᴿ : ∀ a →
      A⊥ᴿ (⨆ a) ≡ ⨆ᴬ (Seqᴿ a)
    ⟦_⟧ᴿ : ∀ a i →
      A⊥ᴿ (⟦ a ⟧ i) ≡ ⟦ Seqᴿ a ⟧ᴬ i
    _,_ᴿ : ∀ f p →
      Seqᴿ (f , p) ≡ ((λ i → A⊥ᴿ (f i)) ,ᴬ (λ i → ≤ᴿ (p i)))
    ≤reflᴿ : ∀ {x} →
      ≤ᴿ (≤refl {x}) ≡ ≤reflᴬ
    ≤transᴿ : ∀ {x y z} (p : x ≤ y) (q : y ≤ z) →
      ≤ᴿ (≤trans p q) ≡ ≤transᴬ (≤ᴿ p) (≤ᴿ q)
    ⊥≤ᴿ : ∀ {x} →
      subst (λ z → z ≤ᴬ A⊥ᴿ x) ⊥ᴿ (≤ᴿ (⊥≤ {x}))
        ≡ ⊥≤ᴬ
    ≤⨆ᴿ : ∀ a i →
      ≡.subst₂ _≤ᴬ_ (⟦ a ⟧ᴿ i) (⨆ᴿ a) (≤ᴿ (≤⨆ a i))
        ≡ ≤⨆ᴬ (Seqᴿ a) i
    ⨆≤ᴿ : ∀ a x (p : ∀ i → ⟦ a ⟧ i ≤ x) →
      subst (λ z → z ≤ᴬ A⊥ᴿ x) (⨆ᴿ a) (≤ᴿ (⨆≤ a x p))
        ≡ ⨆≤ᴬ (Seqᴿ a) (A⊥ᴿ x)
            (λ i → subst (λ z → z ≤ᴬ A⊥ᴿ x) (⟦ a ⟧ᴿ i) (≤ᴿ (p i)))
    incᴿ : ∀ a i →
      ≡.subst₂ _≤ᴬ_ (⟦ a ⟧ᴿ i) (⟦ a ⟧ᴿ (suc i)) (≤ᴿ (inc a i))
        ≡ incᴬ (Seqᴿ a) i
    ≈antisymᴿ : ∀ {x y} (p : x ≤ y) (q : y ≤ x) →
      ≈ᴿ (≈antisym p q) ≡ ≈antisymᴬ (≤ᴿ p) (≤ᴿ q)
  

module Properties where
  ≈refl : ∀ {x} → x ≈ x
  ≈refl = ≈antisym ≤refl ≤refl
  ≤cong⨆ : ∀ {f g : ℕ → A⊥} {f≤ g≤} → (∀ i → f i ≤ g i) → ⨆ (f , f≤) ≤ ⨆ (g , g≤)
  ≤cong⨆ {f} {g} {f≤} {g≤} p = ⨆≤ (f , f≤) (⨆ (g , g≤))
    λ i → ≤cong (≈sym (η,⟦⟧ f f≤ i))
                ≈refl
                (≤trans (p i)
                (≤trans (≈→≤ (≈sym (η,⟦⟧ g g≤ i)))
                        (≤⨆ (g , g≤) i)))
  ≈cong⨆ : ∀ {f g : ℕ → A⊥} {f≤ g≤} → (∀ i → f i ≈ g i) → ⨆ (f , f≤) ≈ ⨆ (g , g≤)
  ≈cong⨆ {f} {g} {f≤} {g≤} p = ≈antisym (≤cong⨆ (λ i → ≈→≤ (p i))) (≤cong⨆ (λ i → ≈→≤ (≈sym (p i))))
