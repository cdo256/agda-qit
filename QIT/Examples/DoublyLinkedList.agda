module QIT.Examples.DoublyLinkedList where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Nullary
open import QIT.Nat
open import Data.Maybe

record Algebra (X : Set) : Set₁ where
  field
    DLL  : ℕ → Set
    Node : ∀ {n} → DLL n → Set
    Val  : ∀ {n} {xs : DLL n} → Node xs → Maybe X → Set

    ∅    : DLL zero
    ins  : ∀ {n} → X → (xs : DLL n)
         → Node xs → DLL (suc n)
    del : ∀ {n x} → (xs : DLL (suc n))
         → (a : Node xs)
         → Val a (just x) → DLL n

    root : ∀ {n} {xs : DLL n} → Node xs
    σ-ins : ∀ {n} {xs : DLL n} (x : X)
          → (a : Node xs) → Node (ins x xs a)
    σ-del : ∀ {n x} (xs : DLL (suc n))
           → (a : Node xs)
           → Val a (just x)
           → Node (del xs a {!!})

    ins∘del : ∀ {x n} → (xs : DLL (suc n))
           → (a : Node xs)
           → (val-a : Val a (just x))
           → ins x (del xs a {!!}) (σ-del xs a val-a) ≡ xs
    del∘ins : ∀ {x z n} → (xs : DLL (suc n))
           → (a : Node xs)
           → (val-a : Val (σ-ins x a) (just z))
           → del (ins x xs a) (σ-ins x a) val-a ≡ xs

    next prev : ∀ {n} {xs : DLL n} → Node xs → Node xs
    π-root : ∀ {n xs x} → σ-ins {n} {xs} x root ≡ root
    loop-r : ∀ {n xs} → (a : Node {n} xs)
           → iter a next n ≡ a
    loop-l : ∀ {n xs} → (a : Node {n} xs)
           → iter a prev n ≡ a
    next∘prev : ∀ {n xs} → (a : Node {n} xs)
              → next (prev a) ≡ a
    prev∘next : ∀ {n xs} → (a : Node {n} xs)
              → prev (next a) ≡ a

    val-ins : ∀ {n} → (x? : Maybe X) (y : X)
          → (xs : DLL n)
          → (a : Node xs)
          → Val (next (next (σ-ins y a))) x?
          → Val (next a) x?
    val-insʳ : ∀ {n} → (x? : Maybe X) (y : X)
          → (xs : DLL n)
          → (a : Node xs)
          → Val (next a) x?
          → Val (next (next (σ-ins y a))) x?
    
    val-del : ∀ {n z} → (x? : Maybe X) (y : X)
          → (xs : DLL (suc n))
          → (a : Node xs)
          → (val-a : Val a (just z))
          → Val (next (σ-del xs a val-a)) x?
          → Val (next (next a)) x?
    val-delʳ : ∀ {n z} → (x? : Maybe X) (y : X)
          → (xs : DLL (suc n))
          → (a : Node xs)
          → (val-a : Val a (just z))
          → Val (next (next a)) x?
          → Val (next (σ-del xs a val-a)) x?
    
    -- π∷ : (x : X) {xs : DLL} (a : Node xs) → Node (x ∷ a)
    -- π∷⁻ : (x : X) {xs : DLL} (a : Node xs) → Node (a ∷⁻ x)
    -- next∘π∷ : ∀ {xs} → (x : X) (a : Node xs) → Val (next (π∷ x a)) x
    -- prev∘π∷⁻ : ∀ {xs} → (x : X) (a : Node xs) → Val (prev (π∷⁻ x a)) x
    -- isRightUniqueVal : ∀ {xs} → (a : Node xs) → isProp (Σ _ (Val a))
    
