open import QIT.Prelude

module QIT.Examples.ConTy.Iterated ⦃ a!c* : A!C ⦄ where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base
open import QIT.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; ≤-refl; m≤n⇒m≤1+n; n≤1+n)

-- Iterated ConTy algebra.
--
-- Each sort is indexed by a natural number "level".  Every constructor
-- produces a result at a *strictly higher* level than the context it
-- consumes, ensuring well-foundedness.
--
-- The key design choices:
--
--   ιC : (p : i ≤ j) → Con i → Con j
--
--   Using a target level j with a ≤-proof (non-strict) avoids the
--   definitional-arithmetic issues that arise with offset-based n+i.
--   Both sides of ι▷ land in Con (suc j):
--
--     ιC (s≤s p) (γ ▷ a) : Con (suc j)   (since γ▷a : Con (suc i))
--     ιC p γ ▷ ιT p γ a  : Con (suc j)   (since ιC p γ : Con j)
--
--   This equality holds definitionally with no arithmetic needed.
--
--   ιC-irr captures proof-irrelevance of ιC in its ≤-argument.
--   This is needed in σπ where ≤+2 {suc i} and s≤s (≤+2 {i}) are
--   propositionally but not definitionally equal as ≤-proofs.

-- Shorthands for the ≤-proofs we actually use.

≤+1 : ∀ {i} → i ≤ suc i
≤+1 = n≤1+n _

≤+2 : ∀ {i} → i ≤ suc (suc i)
≤+2 = m≤n⇒m≤1+n ≤+1

record ItAlgebra : Set₁ where
  infixl 5 _▷_
  field
    -- Sorts, indexed by level.
    Con : ℕ → Set
    Ty  : ∀ {i} → Con i → Set

    -- Weakening: promote a context from level i to any higher level j.
    ιC  : ∀ {i j} → i ≤ j → Con i → Con j
    -- Promote a type along the same inclusion.
    ιT  : ∀ {i j} (p : i ≤ j) (γ : Con i) → Ty γ → Ty (ιC p γ)

    -- ιC depends only on the endpoint, not the proof.
    -- (Holds automatically in any model where Con i is a set.)
    ιC-irr : ∀ {i j} (p q : i ≤ j) (γ : Con i) → ιC p γ ≡ ιC q γ

    -- Empty context at every level.
    ∙   : ∀ {i} → Con i

    -- Context extension raises the level by exactly 1.
    --   γ   : Con i       a   : Ty γ
    --   γ▷a : Con (suc i)          — strictly above γ  ✓
    _▷_ : ∀ {i} (γ : Con i) → Ty γ → Con (suc i)

    -- ι commutes with ▷.
    --
    --   ιC (s≤s p) (γ ▷ a)  ≡  ιC p γ ▷ ιT p γ a
    --
    -- Level check (p : i ≤ j):
    --   LHS : γ▷a : Con (suc i);  s≤s p : suc i ≤ suc j  →  Con (suc j)
    --   RHS : ιC p γ : Con j;      ▷ raises by 1          →  Con (suc j)  ✓
    ι▷  : ∀ {i j} (p : i ≤ j) (γ : Con i) (a : Ty γ)
         → ιC (s≤s p) (γ ▷ a) ≡ ιC p γ ▷ ιT p γ a

    -- ι-type: lives one level above its context.
    --   u γ : Ty (ιC ≤+1 γ)   where  ≤+1 : i ≤ suc i
    --   level of result = suc i  >  i  ✓
    u   : ∀ {i} (γ : Con i) → Ty (ιC ≤+1 γ)

    -- Π-type: takes types at levels i and i+1, lives two levels above γ.
    --   a : Ty γ               level i
    --   b : Ty (γ ▷ a)         level i+1
    --   π γ a b : Ty (ιC ≤+2 γ)   level suc(suc i) > i+1 > i  ✓
    π   : ∀ {i} (γ : Con i) (a : Ty γ) (b : Ty (γ ▷ a))
         → Ty (ιC ≤+2 γ)

    -- Σ-type: same signature as π.
    σ   : ∀ {i} (γ : Con i) (a : Ty γ) (b : Ty (γ ▷ a))
         → Ty (ιC ≤+2 γ)

    -- Context-substitution equation.
    --
    -- In Direct:  γ ▷ a ▷ b  ≡  γ ▷ σ a b
    --
    -- In the iterated setting the two sides live at different levels:
    --   γ ▷ a ▷ b  : Con (suc (suc i))                     level i+2
    --   γ ▷ σ a b  : Con (suc (suc (suc i)))               level i+3
    --     (because σ a b : Ty (ιC ≤+2 γ) over Con (suc(suc i)),
    --      so ▷ raises to Con (suc(suc(suc i))))
    --
    -- We promote the LHS by one step to reach the same level:
    --
    --   ιC ≤+1 (γ ▷ a ▷ b)  ≡  ιC ≤+2 γ ▷ σ γ a b  :  Con (suc(suc(suc i)))
    --
    -- Level check  (≤+1 here has implicit i = suc(suc i)):
    --   LHS : suc(suc i) ≤ suc(suc(suc i))  →  Con (suc(suc(suc i)))  ✓
    --   RHS : ιC ≤+2 γ : Con (suc(suc i));
    --         σ γ a b : Ty (ιC ≤+2 γ);
    --         ▷ gives Con (suc(suc(suc i)))                             ✓
    σ▷  : ∀ {i} (γ : Con i) (a : Ty γ) (b : Ty (γ ▷ a))
         → ιC ≤+1 (γ ▷ a ▷ b) ≡ ιC ≤+2 γ ▷ σ γ a b

    -- Associativity of Π under Σ.
    --
    -- In Direct:  π a (π b c)  ≡  π (σ a b) (subst Ty σ▷ c)
    --
    -- Variables:
    --   γ : Con i
    --   a : Ty γ                  level i
    --   b : Ty (γ ▷ a)            level i+1
    --   c : Ty (γ ▷ a ▷ b)        level i+2
    --
    -- Inner π:
    --   π (γ ▷ a) b c  :  Ty (ιC ≤+2 (γ ▷ a))
    --   ≤+2 has implicit i = suc i, so target = suc(suc(suc i))
    --
    -- To feed the inner π as the third argument of the outer π, we
    -- need it at  Ty (ιC ≤+2 γ ▷ ιT ≤+2 γ a).
    --
    -- From ι▷ (≤+2 {i}) γ a:
    --   ιC (s≤s ≤+2) (γ ▷ a) ≡ ιC ≤+2 γ ▷ ιT ≤+2 γ a
    --   (both at Con (suc(suc(suc i))))
    --
    -- But  π (γ▷a) b c  lives in  Ty (ιC (≤+2 {suc i}) (γ▷a)).
    -- The proofs  ≤+2 {suc i}  and  s≤s (≤+2 {i})  are both of type
    --   suc i ≤ suc(suc(suc i))
    -- and differ only as proof terms; ιC-irr equates the two Con-values.
    --
    -- LHS:
    --   π (ιC ≤+2 γ) (ιT ≤+2 γ a)
    --     (subst Ty
    --       (≡.trans (ιC-irr ≤+2 (s≤s ≤+2) (γ ▷ a))
    --                (ι▷ ≤+2 γ a))
    --       (π (γ ▷ a) b c))
    --   : Ty (ιC ≤+2 (ιC ≤+2 γ))   — level suc(suc(suc(suc i)))
    --
    -- RHS:
    --   ιT ≤+1 (γ ▷ a ▷ b) c  :  Ty (ιC ≤+1 (γ ▷ a ▷ b))  at Con(suc³i)
    --   σ▷ γ a b               :  ιC ≤+1 (γ▷a▷b) ≡ ιC ≤+2 γ ▷ σ γ a b
    --   subst Ty (σ▷ γ a b) (ιT ≤+1 (γ▷a▷b) c)
    --                          :  Ty (ιC ≤+2 γ ▷ σ γ a b)
    --
    --   π (ιC ≤+2 γ) (σ γ a b)
    --     (subst Ty (σ▷ γ a b) (ιT ≤+1 (γ ▷ a ▷ b) c))
    --   : Ty (ιC ≤+2 (ιC ≤+2 γ))   ✓  same level as LHS
    σπ  : ∀ {i} (γ : Con i) (a : Ty γ) (b : Ty (γ ▷ a)) (c : Ty (γ ▷ a ▷ b))
         → π (ιC ≤+2 γ) (ιT ≤+2 γ a)
               (subst Ty
                 (≡.trans (ιC-irr ≤+2 (s≤s ≤+2) (γ ▷ a))
                          (ι▷ ≤+2 γ a))
                 (π (γ ▷ a) b c))
         ≡ π (ιC ≤+2 γ) (σ γ a b)
               (subst Ty (σ▷ γ a b) (ιT ≤+1 (γ ▷ a ▷ b) c))

open ItAlgebra public
