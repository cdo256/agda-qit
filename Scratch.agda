open import QIT.Prelude
open import QIT.Prop

module Scratch
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.List
open import QIT.Maybe

module _ (A : Set) where
  record Q1 : Set where
    constructor q1
    field
      list : List A
  push1 : A → Q1 → Q1
  push1 x (q1 xs) = q1 (x ∷ xs)
  pop1 : Q1 → Maybe (A × Q1)
  pop1 (q1 []) = nothing
  pop1 (q1 (x ∷ xs)) = map (λ (y , q1 ys) → y , q1 (x ∷ ys)) (pop1 (q1 xs))
      
  record Q2 : Set where
    constructor q2
    field
      fwd : List A
      bwd : List A
  -- {-# TERMINATING #-}
  flip : Q2 → Q2
  flip (q2 xs []) = q2 xs []
  flip (q2 [] (y ∷ ys)) with flip (q2 [] ys)
  ... | q2 xs' ys' = q2 (y ∷ xs') ys'
  flip (q2 (x ∷ xs) (y ∷ ys)) with flip (q2 xs (y ∷ ys))
  ... | q2 xs' ys' = q2 (x ∷ xs') ys'

  postulate
    flip-bwd-empty : ∀ (q : Q2) → flip q .Q2.bwd ≡ []

  push2 : A → Q2 → Q2
  push2 x (q2 xs ys) = q2 (x ∷ xs) ys
  pop2 : Q2 → Maybe (A × Q2)
  pop2 (q2 [] []) = nothing
  pop2 (q2 (x ∷ xs) ys) =
    map (λ (y , q2 xs' ys') → y , q2 (x ∷ xs') ys')
        (pop2 (q2 xs ys))
  pop2 (q2 [] (y ∷ ys)) = just (y , q2 [] ys)

  []≢∷ : ∀ {x : A} {xs} → [] ≢ (x ∷ xs)
  []≢∷ ()

  flatten1 : Q1 → List A
  flatten1 q = q .Q1.list
  flatten2 : Q2 → List A
  flatten2 q with flip q
  ... | q2 xs [] = xs
  ... | q'@(q2 xs (y ∷ ys)) =
    -- This doesn't compute since the with clause doesn't know that
    -- flip q is the matched expression.
    ⊥e' ([]≢∷ (≡.sym {x = y ∷ ys} {y = []} {!flip-bwd-empty q'!}))

  data br : Q1 → Q2 → Set where
    fl : ∀ q1 q2 → flatten1 q1 ≡ flatten2 q2 → br q1 q2 
     
