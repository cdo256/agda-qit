module QIT.Relation.BarInduction where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import Data.Nat
open import Data.List
-- open import Data.Sigma
open import Data.Sum
open import Data.Maybe
open import Data.Empty
open import QIT.Container.Base

module _ {ℓ} (A : Set ℓ) where
  FinSeq = List A
  InfSeq = ℕ → A

  prefix : ℕ → InfSeq → FinSeq
  prefix zero α = []
  prefix (suc n) α = α 0 ∷ prefix n λ i → α (suc i)

  prefixFin : ℕ → FinSeq → Maybe FinSeq
  prefixFin zero xs = just []
  prefixFin (suc n) [] = nothing
  prefixFin (suc n) (x ∷ xs) =
    Data.Maybe.map (x ∷_) (prefixFin n xs)

  isBar : (B : FinSeq → Prop ℓ) → Prop ℓ
  isBar B = ∀ (α : InfSeq) → ∃ λ i → B (prefix i α)

  MaybeProp→Prop : Maybe (Prop ℓ) → Prop ℓ
  MaybeProp→Prop nothing = ⊥p*
  MaybeProp→Prop (just X) = X

  FinSeqCrossesBar
    : (B : FinSeq → Prop ℓ)
    → (xs : FinSeq) → Prop ℓ
  FinSeqCrossesBar B xs = ∃ λ i →
    MaybeProp→Prop (Data.Maybe.map B (prefixFin i xs))

  data Bar {ℓ} {A : Set ℓ} (P : List A → Set ℓ)
       : (xs : List A) → Set ℓ where
    now   : ∀ xs → P xs → Bar P xs
    later : ∀ xs → (∀ x → Bar P (x ∷ xs)) → Bar P xs

  module BarInduction
         (P : FinSeq → Set ℓ)
         (Q : FinSeq → Set ℓ)
         where

    BaseType : Set ℓ
    BaseType = ∀ xs → P xs → Q xs

    InductiveType : Set ℓ
    InductiveType = ∀ xs → (∀ x → Q (x ∷ xs)) → Q xs

    barInduction 
      : ∀ xs (B : Bar P xs) → BaseType
      → InductiveType → Q xs
    barInduction xs (now xs pxs) base ind = base xs pxs
    barInduction xs (later xs pch) base ind =
      ind xs u
      where
      u : (y : A) → Q (y ∷ xs)
      u y with pch y
      ... | now (x ∷ xs) pxxs = base (x ∷ xs) pxxs
      ... | later (x ∷ xs) Pxxxs =
        barInduction (y ∷ xs) (pch y) base ind
