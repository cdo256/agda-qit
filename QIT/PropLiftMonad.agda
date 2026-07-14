open import QIT.Prelude
open import QIT.Prop
open import QIT.Function.Base
open import QIT.Set.Bijection 

module QIT.PropLiftMonad
  ⦃ pathElim* : PathElim ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ funExt* : FunExt ⦄
  where

open PropExt propExt*
open FunExt funExt*

record PropLift ℓP (X : Set ℓX) : Set (lsuc ℓP ⊔ ℓX) where
  constructor _,_
  field
    Cond : Prop ℓP
    val : Cond → X

open PropLift public

module _ {ℓP} where
  return : {X : Set ℓX} → X → PropLift ℓP X
  return x = ⊤* , λ _ → x
  fail : {X : Set ℓX} → PropLift ℓP X
  fail = ⊥* , λ ()
  assume : {X : Set ℓX} → (P : Prop ℓP) → (P → PropLift ℓP X) → PropLift ℓP X
  assume P x* = (P ∧ᵖ (λ p → x* p .Cond)) , λ (∧i p , q) → x* p .val q
  _>>=_ : {X : Set ℓX} {Y : Set ℓY} → PropLift ℓP X → (X → PropLift ℓP Y) → PropLift ℓP Y
  (P , x) >>= f = (P ∧ᵖ λ p → f (x p) .Cond) , λ (∧i p , q) → f (x p) .val q
  _>>_ : {X : Set ℓX} {Y : Set ℓY} → PropLift ℓP X → PropLift ℓP Y → PropLift ℓP Y
  x* >> y* = x* >>= λ _ → y*
  _<*>_ : {X : Set ℓX} {Y : Set ℓY} → PropLift ℓP (X → Y) → PropLift ℓP X → PropLift ℓP Y
  _<*>_ (P , f) (Q , x) = (P , f) >>= λ f → Q , λ q → f (x q)
  map : {X : Set ℓX} {Y : Set ℓY} → (X → Y) → PropLift ℓP X → PropLift ℓP Y
  map f x* = return f <*> x*

  _↓ : ∀ {X : Set ℓX} → PropLift ℓP X → Prop ℓP
  (P , _) ↓ = P

  _≈_ : ∀ {ℓA} {X : Set ℓA} → PropLift ℓP X → PropLift ℓP X → Prop _
  (P , f) ≈ (Q , g) =
    (P ⇔ Q) ∧ ∀ p q → f p ≡ g q

  PropLift≡ : {X : Set ℓX} {x* y* : PropLift ℓP X}
    → (p : x* .Cond ≡ y* .Cond)
    → (q : subst (_↝ X) p (x* .val) ≡ (y* .val))
    → x* ≡ y*
  PropLift≡ ≡.refl ≡.refl = ≡.refl

  ≈→≡ : ∀ {ℓA} {X : Set ℓA} → {x* y* : PropLift ℓP X} → x* ≈ y* → x* ≡ y*
  ≈→≡ {X = X} {P , f} {Q , g} (∧i p⇔q , f≡g) = PropLift≡ (propExt p⇔q) (r (propExt p⇔q))
    where
    r : (pq : P ≡ Q) → ≡.subst (λ ○ → ○ → X) pq f ≡ g
    r ≡.refl = funExtp λ p → f≡g p p

  ≈refl : ∀ {ℓA} {X : Set ℓA} → (x* : PropLift ℓP X) → x* ≈ x*
  ≈refl (P , f) = ∧i ∧i (λ z → z) , (λ z → z) , λ _ _ → ≡.refl

  ≡→≈ : ∀ {ℓA} {X : Set ℓA} → {x* y* : PropLift ℓP X} → x* ≡ y* → x* ≈ y*
  ≡→≈ {x* = x*} {y*} p = substp (x* ≈_) p (≈refl x*)

  return-inj : {X : Set ℓX} {x y : X} → return x ≡ return y → x ≡ y
  return-inj {ℓX} {X} {x} {y} p =
    ≡.funExtp⁻ r tt*
    where
    q : Cond (return x) ≡ Cond (return y)
    q = ≡.cong Cond p
    r : ≡.subst (_↝ X) q (val (return x)) ≡ val (return y)
    r = ≡.dcong-∘ (_↝ X) (PropLift ℓP X) Cond val p
    open ≡.≡-Reasoning

  map-inj : {X : Set ℓX} {Y : Set ℓY} → (f : X → Y) → {x* y* : PropLift ℓP X}
    → map f x* ≡ map f y*
    → IsInjection f
    → x* ≡ y*
  map-inj {ℓX} {ℓY} {X} {Y} f {P , x} {Q , y} map≡ inj-f =
    ≈→≡ (∧i P⇔Q , r)
    where
    map≈ : map f (P , x) ≈ map f (Q , y)
    map≈ = ≡→≈ map≡
    open ≡.≡-Reasoning
    ⊤' = LiftP ℓP ⊤
    p'→q' : ⊤' ∧ P → (⊤' ∧ Q)
    p'→q' = map≈ .∧e₁ .∧e₁
    q'→p' : (⊤' ∧ Q) → (⊤' ∧ P)
    q'→p' = map≈ .∧e₁ .∧e₂
    u : (p : ⊤' ∧ P) (q : ⊤' ∧ Q)
      → f (x (p .∧e₂)) ≡ f (y (q .∧e₂))
    u = map≈ .∧e₂
    p→q : P → Q
    p→q p = p'→q' (∧i tt* , p) .∧e₂ 
    q→p : Q → P
    q→p q = q'→p' (∧i tt* , q) .∧e₂
    P⇔Q : P ⇔ Q
    P⇔Q = ∧i p→q , q→p
    r : (p : P) (q : Q) → x p ≡ y q
    r p q =
      inj-f (u (∧i tt* , p) (∧i tt* , q))

  map-return-inj : {X : Set ℓX} {Y : Set ℓY} → (f : X → Y)
    → (x* : PropLift ℓP X) (y : Y)
    → map f x* ≡ return y
    → ΣP X λ x → f x ≡ y
  map-return-inj f (P , x) y m≡r = x p , u
    where
    m≈r : map f (P , x) ≈ return y
    m≈r = ≡→≈ m≡r
    p : P
    p = m≈r .∧e₁ .∧e₂ tt* .∧e₂
    u : f (x p) ≡ y
    u = m≈r .∧e₂ (∧i tt* , p) tt*
    
  map≢return : {X : Set ℓX} {Y : Set ℓY} (f : X → Y)
    → (x* : PropLift ℓP X) (y : Y)
    → (∀ x → f x ≢ y)
    → map f x* ≢ return y
  map≢return f x* y fx≢y m≡r =
    let x , u = map-return-inj f x* y m≡r in fx≢y x u
