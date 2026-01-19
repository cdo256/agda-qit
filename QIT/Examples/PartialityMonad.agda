module QIT.Examples.PartialityMonad where

open import QIT.Prelude renaming (⊤ to ⊤'; ⊥ to ⊥') hiding (_≟_)
open import QIT.Relation.Subset
import Data.Nat as ℕ
open ℕ using (ℕ; zero; suc)
import Data.Bool as 𝔹 
open 𝔹 using (Bool; false; true)

import Data.Integer as ℤ 
open ℤ using (ℤ)

mutual
  record Seq : Set where
    inductive
    constructor _,_
    field
      ⟦_⟧ : ℕ → PM
      inc : ∀ i → ⟦_⟧ i ≤ ⟦_⟧ (suc i)

  data PM : Set where
    η : Bool → PM
    ⊥ : PM
    ⨆ : (a : Seq) → PM

  data _≤_ : PM → PM → Prop where
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ⊥≤ : ∀ {x} → ⊥ ≤ x
    ≤⨆ : ∀ a i → Seq.⟦ a ⟧ i ≤ ⨆ a
    ⨆≤ : ∀ a x → (∀ i → Seq.⟦ a ⟧ i ≤ x) → ⨆ a ≤ x

  data _≈_ : PM → PM → Prop where
    ≈antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

≤cong : ∀ {x x' y y'} → x ≈ x' → y ≈ y' → x ≤ y → x' ≤ y'
≤cong (≈antisym x≤x' x'≤x) (≈antisym y≤y' y'≤y) x≤y = ≤trans x'≤x (≤trans x≤y y≤y')

module TM (Σ : Set) (_≟Σ_ : Discrete Σ) where
  Σ' = Σ ⊎ ⊤'
  
  record TM : Set₁ where
    field
      S : Set
      _≟ˢ_ : Discrete S
      accept reject : S
      δ : S × Σ' → S × Σ' × ℤ

  record State (M : TM) : Set₁ where
    open TM M
    field
      tape : ℤ → Σ'
      s : S

  module _ where
    -- hack
    import Relation.Nullary.Decidable.Core as DecCore
    infix 4 _≟ᶻ_
    _≟ᶻ_ : Discrete ℤ
    m ≟ᶻ n with m ℤ.≟ n
    ... | DecCore.yes p = yes p
    ... | DecCore.no ¬p = no ¬p

  step : (M : TM) → State M → State M
  step M state with s ≟ˢ accept | s ≟ˢ reject | δ (s , tape (ℤ.+ zero))
    where
    open TM M
    open State state
  ... | yes _ | _ | _ = state
  ... | no _ | yes _ | _ = state
  ... | no _ | no _ | (s' , (σ' , n)) = record { tape = tape' ; s = s' }
    where
    open TM M
    open State state
    tape' : ℤ → Σ'
    tape' = λ i → if i ≟ᶻ n then σ' else tape (i ℤ.- n)

module _ {X : Set} (enc : (X → Seq) → X) (unenc : X → (X → Seq)) where
  Halts : (X → Seq) → Prop
  Halts M = ∀ a → ∃ λ x → η x ≈ ⨆ (M a)

  record Decides (A : X → Prop) (M : X → Seq) : Prop where
    field
      halts : Halts M
      accepts : ∀ a → η true ≈ ⨆ (M a) ⇔ A a

  record DecidesHalt (M : X → Seq) : Prop where
    field
      halts : Halts M
      accepts : ∀ N → η true ≈ ⨆ (M (enc N)) ⇔ Halts N

  H : X → Seq
  H x = a , {!!}
    where
    a : ℕ → PM
    a i = {!!}
