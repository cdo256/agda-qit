module QIT.Examples.Lambda.Nominal where

open import QIT.Prelude
open import QIT.Prop
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_; _≤_)
open import QIT.Function.Base
open import QIT.Set.Bijection
open import QIT.Relation.Subset
open import QIT.Relation.Nullary

infixl 15 _﹫_
infixl 30 _[_]

record Λ-Algebra (Name : Set) (_≟ᴺ_ : Discrete Name) : Set₁ where
  field
    Λ : Set
    ν : Name → Λ
    _﹫_ : Λ → Λ → Λ
    λ̂ : Name → Λ → Λ
    Free : Λ → Name → Prop
    Free-ν : ∀ n → Free (ν n) n
    Free-﹫₁ : ∀ n s t → Free s n → Free (s ﹫ t) n
    Free-﹫₂ : ∀ n s t → Free t n → Free (s ﹫ t) n
    Free-λ̂ : ∀ m n s → m ≢ n → Free s n → Free (λ̂ m s) n
    -- Inverse forms. TODO: Are these needed?
    -- Free-﹫₁⁻ : ∀ n s t → Free (s ﹫ t) n → Free s n
    -- Free-﹫₂⁻ : ∀ n s t → Free (s ﹫ t) n → Free t n
    -- Free-λ̂⁻ : ∀ m n s → m ≢ n → Free (λ̂ m s) n → Free s n 

    -- FIXME: I started implementing rename free variables, not bound
    -- variables. This needs changing
--     rename : ∀ s → (f : ΣP Name (Free s) → Name)
--            → IsInjection f → Λ
--     rename-ν : (n : Name)
--              → (f : ΣP Name (Free (ν n)) → Name)
--              → (inj-f : IsInjection f)
--              → rename (ν n) f inj-f ≡ ν (f (n , Free-ν n))
--     rename-﹫ : ∀ s t
--               → (f : ΣP Name (Free (s ﹫ t)) → Name)
--               → (inj-f : IsInjection f)
--               → let fs : ΣP Name (Free s) → Name
--                     fs (n , Fsn) = f (n , Free-﹫₁ n s t Fsn)
--                     ft : ΣP Name (Free t) → Name
--                     ft (n , Ftn) = f (n , Free-﹫₂ n s t Ftn)
--                 in
--                 rename (s ﹫ t) f inj-f
--               ≡ (rename s fs (injΣP-restrict (Free-﹫₁ _ s t) f inj-f)
--               ﹫ rename t ft (injΣP-restrict (Free-﹫₂ _ s t) f inj-f))
--     rename-λ̂ : ∀ m s
--              → (f : ΣP Name (Free (λ̂ m s)) → Name)
--              → (inj-f : IsInjection f)
--              → let fs : ΣP Name (λ n → m ≢ n ∧ Free s n) → Name
--                    fs (n , m≢n , Fsn) = f (n , Free-λ̂ m n s m≢n Fsn)
--                in
--                rename (λ̂ m s) f inj-f
--              ≡ λ̂ m (rename s {!!} {!!})
