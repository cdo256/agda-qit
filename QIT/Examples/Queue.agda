open import QIT.Prelude

module QIT.Examples.Queue ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Nullary
open import QIT.Nat
open import Data.Maybe

record Algebra (X : Set) : Set₁ where
  field
    Q : Set
    empty : Set
    snoc : X → Q → X
    head : Q → Maybe X
    tail : Q → Q

    
