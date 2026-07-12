open import QIT.Prelude

module QIT.Examples.ConTy.DirectToWeaklyTaggedSmall
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

open PropExt propExt*
open FunExt funExt*

import QIT.Examples.ConTy.Direct as D
import QIT.Examples.ConTy.WeaklyTagged as W

open import QIT.Prelude
open import QIT.Prop
open import QIT.Logic
open import QIT.Types
open import QIT.Maybe using (Maybe)
open import QIT.Category.Morphism
open import QIT.Category.Initial
open import QIT.Relation.Subset
open import QIT.Function.Base

module D→W (da : D.Algebra ℓA) where
  open ≡
  module DA = D.Algebra da
  data Atom : Set ℓA where
    con : DA.Con → Atom
    ty : (γ : DA.Con) → DA.Ty γ → Atom
    k̂ : Atom
    ĉ : Atom
    t̂ : Atom → Atom

  data Hyp : Set ℓA
  ⟦_⟧ : Hyp → Prop ℓA
  infixl 3 _∷_
  infixl 3 _+_
  data Hyp where
    [] : Hyp
    _≛_ : (x y : Atom) → Hyp
    _+p_ : (P : Hyp) → (⟦ P ⟧ → Hyp) → Hyp
  ⟦ [] ⟧ = ⊤*
  ⟦ x ≛ y ⟧ = x ≡ y
  ⟦ P +p Q ⟧ = ⟦ P ⟧ ∧ᵖ λ p → ⟦ Q p ⟧
  _+_ : Hyp → Hyp → Hyp 
  P + Q = P +p λ _ → Q
  CT : Set ℓA
  CT = Σ Hyp (λ xs → ⟦ xs ⟧ → Atom)
  return : Atom → CT
  return x = [] , λ _ → x
  assume : (x y : Atom) → (x ≡ y → CT) → CT
  assume x y P = (x ≛ y) +p (λ x≡y → P x≡y .proj₁) , λ (∧i x≡y , p) → P x≡y .proj₂ p
  _>>=_ : CT → (Atom → CT) → CT
  (P , x) >>= f = (P +p λ p → f (x p) .proj₁)
                , λ (∧i p , q) → f (x p) .proj₂ q
  _>>_ : CT → CT → CT
  x >> y = x >>= λ _ → y
  map : {X : Set ℓX} {Y : Set ℓY} → (Atom → Atom) → CT → CT
  map f (P , x) = P , λ p → f (x p) 

  _≈_ : CT → CT → Prop _
  (P , f) ≈ (Q , g) = (⟦ P ⟧ ⇔ ⟦ Q ⟧) ∧ ∀ p q → f p ≡ g q
