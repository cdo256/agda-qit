open import QIT.Prelude
open import QIT.Prop

module QIT.LiftingMonad
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

open PropExt propExt*
open FunExt funExt*

Lifting : ∀ ℓP (X : Set ℓX) → Set (lsuc ℓP ⊔ ℓX)
Lifting ℓP X = Σ (Prop ℓP) (λ P → P → X)

return : {X : Set ℓX} → X → Lifting ℓP X
return x = ⊤* , λ _ → x
fail : {X : Set ℓX} → Lifting ℓP X
fail = ⊥* , λ ()
assume : {X : Set ℓX} → (P : Prop ℓP) → (P → Lifting ℓP X) → Lifting ℓP X
assume P x = (P ∧ᵖ (λ p → x p .proj₁)) , λ (∧i p , hx) → x p .proj₂  hx
_>>=_ : {X : Set ℓX} {Y : Set ℓY} → Lifting ℓP X → (X → Lifting ℓP Y) → Lifting ℓP Y
(P , x) >>= f = (P ∧ᵖ λ h* → f (x h*) .proj₁) , λ h* → f (x (h* .∧e₁)) .proj₂ (h* .∧e₂)
_>>_ : {X : Set ℓX} {Y : Set ℓY} → Lifting ℓP X → Lifting ℓP Y → Lifting ℓP Y
x >> y = x >>= λ _ → y
_<*>_ : {X : Set ℓX} {Y : Set ℓY} → Lifting ℓP (X → Y) → Lifting ℓP X → Lifting ℓP Y
_<*>_ (hs , f) (gs , x) = (hs , f) >>= λ f → gs , λ g* → f (x g*)
map : {X : Set ℓX} {Y : Set ℓY} → (X → Y) → Lifting ℓP X → Lifting ℓP Y
map f x = return f <*> x

_≈_ : ∀ {ℓA} {X : Set ℓA} → Lifting ℓP X → Lifting ℓP X → Prop _
(P , f) ≈ (Q , g) =
  (P ⇔ Q) ∧ ∀ p q → f p ≡ g q

≈→≡ : ∀ {ℓA} {X : Set ℓA} → {x y : Lifting ℓP X} → x ≈ y → x ≡ y
≈→≡ {X = X} {P , f} {Q , g} (∧i p⇔q , f≡g) = Σ≡ (propExt p⇔q) (r (propExt p⇔q))
  where
  r : (pq : P ≡ Q) → ≡.subst (λ ○ → ○ → X) pq f ≡ g
  r ≡.refl = funExtp λ p → f≡g p p
