module QIT.Examples.PartialityMonad.MutualAlgebra where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥')
open import QIT.Prop
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹
open 𝔹 using (Bool; false; true)

record Algebra : Set₁ where
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
