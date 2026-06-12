module QIT.Examples.DoublyLinkedList where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Nullary
open import QIT.Nat hiding (_≤_; _<_)
open import Data.Maybe

record CyclicType : Set₁ where
  field
    I : Set -- index
    

record Algebra (X : Set) : Set₁ where
  field
    DLL : ℕ → Set
    Cursor : ∀ {n} → DLL n → Set
    _<_ : ∀ {n} {xs : DLL n} (i j : Cursor xs) → Set  
    Cmp : ∀ {n} {xs : DLL n}
        → Cursor xs → Cursor xs → Set
    Op : ∀ {n} {xs : DLL n}
       → (i : Cursor xs) → ℕ → Set
    Val : ∀ {n} → DLL n → Maybe X → Set

    lt : ∀ {n xs} {i j : Cursor {n} xs}
      → i < j
      → Cmp i j

    eq : ∀ {n xs} {i j : Cursor {n} xs}
      → i ≡ j
      → Cmp i j

    gt : ∀ {n xs} {i j : Cursor {n} xs}
      → j < i
      → Cmp i j

    ∅ : DLL 0
    begin : ∀ {n} → (xs : DLL (0 + n))
          → Cursor xs
    end : ∀ {n} → (xs : DLL (n + 0))
        → Cursor xs → Cursor xs
    prev : ∀ {n} → (xs : DLL n)
         → Cursor xs → Cursor xs
    next : ∀ {n} → (xs : DLL n)
         → Cursor xs → Cursor xs

    ins-l  : ∀ {m} → X → (xs : DLL m)
           → (i : Cursor xs)
           → Op i (suc m)
    apply : ∀ {m n} → {xs : DLL m}
          → (i : Cursor xs) → Op i n
          → DLL n 
    apply∘ins-l
      : ∀ {x m} → {xs : DLL m}
      → (i : Cursor xs)
      → (j : Cursor xs)
      → Val (apply j (ins-l x xs j)) (just x)
--     ins-r  : ∀ {m n} → X → (xs : DLL (m + n))
--            → (i : Cursor m n xs)
--            → Op i m (suc n)
--     del-l  : ∀ {m n} → (xs : DLL (suc m + n))
--            → (i : Cursor (suc m) n xs)
--            → Op i m n
--     del-r  : ∀ {m n} → (xs : DLL (m + suc n))
--            → (i : Cursor m (suc n) xs)
--            → Op i m n
--     write : ∀ {m n} → Maybe X
--           → (xs : DLL (m + n))
--           → (i : Cursor m n xs)
--           → Op i m n

--     apply : ∀ {m n m' n'}
--           → (xs : DLL (m + n))
--           → (i : Cursor m n xs)
--           → (ρ : Op i m' n')
--           → DLL (m' + n')
--     σ : ∀ {m n m' n' x x'}
--       → (xs : DLL (m + n))
--       → (i : Cursor m n xs)
--       → (p : m + n ≡ x + x')
--       → (j : Cursor x x' (subst DLL p xs))
--       → (ρ : Op i m' n')
--       → Cursor {!!} {!!} (subst DLL {!!} (apply xs i ρ))

    

    

-- -- record Algebra (X : Set) : Set₁ where
-- --   field
-- --     DLL : ℕ → ℕ → Set
-- --     Cursor : ∀ {m n} → DLL m n → Set
-- --     Op : ∀ {m n} → DLL m n → ℕ → ℕ → Set
-- --     Val : ∀ {m n} → DLL m n → Maybe X → Set

-- --     ∅ : DLL 0 0
-- --     rootc : ∀ {m n} → (xs : DLL m n) → Cursor xs
-- --     prevc : ∀ {m n} → (xs : DLL (suc m) n)
-- --           → Cursor xs → Cursor 

-- --     ins-l  : ∀ {m n} → X → (xs : DLL m n) → Op xs (suc m) n
-- --     ins-r  : ∀ {m n} → X → (xs : DLL m n) → Op xs m (suc n)
-- --     del-l : ∀ {m n} → (xs : DLL (suc m) n) → Op xs m n
-- --     del-r : ∀ {m n} → (xs : DLL m (suc n)) → Op xs m n
-- --     write : ∀ {m n} → Maybe X → (xs : DLL m n) → Op xs m n

    
    
    

-- -- --     ins-l  : ∀ {m n} → X
-- -- --            → DLL m n → DLL (suc m) n
-- -- --     ins-r  : ∀ {m n} → X
-- -- --            → DLL m n → DLL m (suc n)
-- -- --     -- delete and move left/right resp.
-- -- --     del-l : ∀ {m n} → DLL (suc m) n → DLL m n
-- -- --     del-r : ∀ {m n} → DLL m (suc n) → DLL m n
-- -- --     write : ∀ {m n} → Maybe X → DLL m n → DLL m n

-- -- --     next : ∀ {m n} → DLL m (suc n) → DLL (suc m) n
-- -- --     prev : ∀ {m n} → DLL (suc m) n → DLL m (suc n)

-- -- --     -- It doesn't matter which side you delete from
-- -- --     del-r≡del-l : ∀ {m n} → (xs : DLL (suc m) (suc (suc n)))
-- -- --                 → next (del-r xs)
-- -- --                 ≡ del-l (next (next xs))

-- -- --     next∘prev : ∀ {m n} → (xs : DLL (suc m) n)
-- -- --               → next (prev xs) ≡ xs
-- -- --     prev∘next : ∀ {m n} → (xs : DLL m (suc n))
-- -- --               → prev (next xs) ≡ xs
-- -- --     ins-l∘del
-- -- --       : ∀ {x m n}
-- -- --       → (xs : DLL m (suc n))
-- -- --       → Val (next xs) (just x)
-- -- --       → ins-l x (del-r xs) ≡ next xs
-- -- --     ins-r∘del
-- -- --       : ∀ {x m n}
-- -- --       → (xs : DLL (suc m) n)
-- -- --       → Val (prev xs) (just x)
-- -- --       → ins-r x (del-l xs) ≡ prev xs
-- -- --     val-ins-l
-- -- --       : ∀ {x m n}
-- -- --       → (xs : DLL m n)
-- -- --       → Val (prev (ins-l x xs)) (just x)
-- -- --     val-ins-r
-- -- --       : ∀ {x m n}
-- -- --       → (xs : DLL m n)
-- -- --       → Val (next (ins-r x xs)) (just x)
-- -- --     val-write
-- -- --       : ∀ {m n} (x? : Maybe X) (xs : DLL m n)
-- -- --       → Val (write x? xs) x?

-- -- -- -- record Algebra (X : Set) : Set₁ where
-- -- -- --   field
-- -- -- --     DLL : ℕ → ℕ → Set
-- -- -- --     Val : ∀ {m n} → DLL m n → Maybe X → Set

-- -- -- --     [_]    : X → DLL 0 0
-- -- -- --     ins-l  : ∀ {m n} → X
-- -- -- --            → DLL m n → DLL (suc m) n
-- -- -- --     ins-r  : ∀ {m n} → X
-- -- -- --            → DLL m n → DLL m (suc n)
-- -- -- --     -- delete and move left/right resp.
-- -- -- --     del-l : ∀ {m n} → DLL (suc m) n → DLL m n
-- -- -- --     del-r : ∀ {m n} → DLL m (suc n) → DLL m n
-- -- -- --     write : ∀ {m n} → Maybe X → DLL m n → DLL m n

-- -- -- --     next : ∀ {m n} → DLL m (suc n) → DLL (suc m) n
-- -- -- --     prev : ∀ {m n} → DLL (suc m) n → DLL m (suc n)

-- -- -- --     -- It doesn't matter which side you delete from
-- -- -- --     del-r≡del-l : ∀ {m n} → (xs : DLL (suc m) (suc (suc n)))
-- -- -- --                 → next (del-r xs)
-- -- -- --                 ≡ del-l (next (next xs))

-- -- -- --     next∘prev : ∀ {m n} → (xs : DLL (suc m) n)
-- -- -- --               → next (prev xs) ≡ xs
-- -- -- --     prev∘next : ∀ {m n} → (xs : DLL m (suc n))
-- -- -- --               → prev (next xs) ≡ xs
-- -- -- --     ins-l∘del
-- -- -- --       : ∀ {x m n}
-- -- -- --       → (xs : DLL m (suc n))
-- -- -- --       → Val (next xs) (just x)
-- -- -- --       → ins-l x (del-r xs) ≡ next xs
-- -- -- --     ins-r∘del
-- -- -- --       : ∀ {x m n}
-- -- -- --       → (xs : DLL (suc m) n)
-- -- -- --       → Val (prev xs) (just x)
-- -- -- --       → ins-r x (del-l xs) ≡ prev xs
-- -- -- --     val-ins-l
-- -- -- --       : ∀ {x m n}
-- -- -- --       → (xs : DLL m n)
-- -- -- --       → Val (prev (ins-l x xs)) (just x)
-- -- -- --     val-ins-r
-- -- -- --       : ∀ {x m n}
-- -- -- --       → (xs : DLL m n)
-- -- -- --       → Val (next (ins-r x xs)) (just x)
-- -- -- --     val-write
-- -- -- --       : ∀ {m n} (x? : Maybe X) (xs : DLL m n)
-- -- -- --       → Val (write x? xs) x?

-- -- -- --     -- loop-r : ∀ {n xs} → (a : Node {n} xs)
-- -- -- --     --        → iter a next n ≡ a
-- -- -- --     -- loop-l : ∀ {n xs} → (a : Node {n} xs)
-- -- -- --     --        → iter a prev n ≡ a
-- -- -- --     -- next∘prev : ∀ {n xs} → (a : Node {n} xs)
-- -- -- --     --           → next (prev a) ≡ a
-- -- -- --     -- prev∘next : ∀ {n xs} → (a : Node {n} xs)
-- -- -- --     --           → prev (next a) ≡ a

-- -- -- --     -- val-ins : ∀ {n} → (x? : Maybe X) (y : X)
-- -- -- --     --       → (xs : DLL n)
-- -- -- --     --       → (a : Node xs)
-- -- -- --     --       → Val (next (next (σ-ins y a))) x?
-- -- -- --     --       → Val (next a) x?
-- -- -- --     -- val-insʳ : ∀ {n} → (x? : Maybe X) (y : X)
-- -- -- --     --       → (xs : DLL n)
-- -- -- --     --       → (a : Node xs)
-- -- -- --     --       → Val (next a) x?
-- -- -- --     --       → Val (next (next (σ-ins y a))) x?
    
-- -- -- --     -- val-del : ∀ {n z} → (x? : Maybe X) (y : X)
-- -- -- --     --       → (xs : DLL (suc n))
-- -- -- --     --       → (a : Node xs)
-- -- -- --     --       → (val-a : Val a (just z))
-- -- -- --     --       → Val (next (σ-del xs a val-a)) x?
-- -- -- --     --       → Val (next (next a)) x?
-- -- -- --     -- val-delʳ : ∀ {n z} → (x? : Maybe X) (y : X)
-- -- -- --     --       → (xs : DLL (suc n))
-- -- -- --     --       → (a : Node xs)
-- -- -- --     --       → (val-a : Val a (just z))
-- -- -- --     --       → Val (next (next a)) x?
-- -- -- --     --       → Val (next (σ-del xs a val-a)) x?
    
-- -- -- --     -- -- π∷ : (x : X) {xs : DLL} (a : Node xs) → Node (x ∷ a)
-- -- -- --     -- -- π∷⁻ : (x : X) {xs : DLL} (a : Node xs) → Node (a ∷⁻ x)
-- -- -- --     -- -- next∘π∷ : ∀ {xs} → (x : X) (a : Node xs) → Val (next (π∷ x a)) x
-- -- -- --     -- -- prev∘π∷⁻ : ∀ {xs} → (x : X) (a : Node xs) → Val (prev (π∷⁻ x a)) x
-- -- -- --     -- -- isRightUniqueVal : ∀ {xs} → (a : Node xs) → isProp (Σ _ (Val a))
    
