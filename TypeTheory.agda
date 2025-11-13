module TypeTheory where

open import Prelude public

----------------------------------------------------------------------
-- Propositional extensionality
----------------------------------------------------------------------
postulate
  propext :
    {l : Level}
    {P Q : Prop l}
    → --------------
    (P ↔ Q) → P == Q

----------------------------------------------------------------------
-- Hofmann-style quotient types, using heterogeneous equality
----------------------------------------------------------------------
module quot where
  -- implemented via postulates and rewriting
  postulate
    ty :
      {l m : Level}
      {A : Set l}
      (R : A → A → Prop m)
      → ------------------
      Set l
    mk :
      {l m : Level}
      {A : Set l}
      (R : A → A → Prop m)
      → ------------------
      A → ty R
    eq :
      {l m : Level}
      {A : Set l}
      (R : A → A → Prop m)
      {x y : A}
      → ----------------------
      R x y → mk R x == mk R y
    elim :
      {l m : Level}
      {A : Set l}
      (R : A → A → Prop m)
      {n : Level}
      (B : ty R → Set n)
      (f : ∀ x → B (mk R x))
      (_ : ∀ {x y} → R x y → f x === f y)
      → ---------------------------------
      ∀ t → B t
    comp :
      {l m : Level}
      {A : Set l}
      (R : A → A → Prop m)
      {n : Level}
      (B : ty R → Set n)
      (f : ∀ x → B (mk R x))
      (e : ∀ {x y} → R x y → f x === f y)
      → ---------------------------------
      ∀ x → elim R B f e (mk R x) == f x
  {-# REWRITE comp #-}

  lift :
    {l m : Level}
    {A : Set l}
    {R : A → A → Prop m}
    {n : Level}
    {B : Set n}
    (f : A → B)
    (_ : ∀ {x y} → R x y → f x == f y)
    → -------------------------------
    ty R → B
  lift = elim _ (λ _ → _)

  liftcomp :
    {l m : Level}
    {A : Set l}
    {R : A → A → Prop m}
    {n : Level}
    {B : Set n}
    (f : A → B)
    (e : ∀ {x y} → R x y → f x == f y)
    → -------------------------------
    ∀ x → lift f e (mk R x) == f x
  liftcomp = λ _ _ _ → refl

  ind :
    {l m : Level}
    {A : Set l}
    (R : A → A → Prop m)
    {n : Level}
    (P : ty R → Prop n)
    (f : ∀ x → P (mk R x))
    → --------------------
    ∀ t → P t
  ind R P f t =
    ↓prop (elim R
      (LiftProp ∘ P)
      (λ x → ↑prop (f x))
      (λ r → ===irrel (ap P (eq R r)))
      t)

  surjectionmk :
    {l m : Level}
    {A : Set l}
    (R : A → A → Prop m)
    → ------------------
    surjection (mk R)
  surjectionmk {A = A} R =
    ind R (λ z → ∃ x ∶ A , mk R x == z) λ x → (∃i x refl)

  -- Function extensionality from quotients
  funext :
    {l m : Level}
    {A : Set l}
    {B : A → Set m}
    {f g : (x : A) → B x}
    (_ : ∀ x → f x == g x)
    → --------------------
    f == g
  funext {A = A} {B} {f} {g} e = ap m (eq 𝕀₂ {x = O} {I} ⊤i)
    where
      data 𝕀 : Set where
        O : 𝕀
        I : 𝕀
      𝕀₂ : 𝕀 → 𝕀 → Prop
      𝕀₂ _ _ = ⊤

      k : (x : A) → 𝕀 → B x
      k x O = f x
      k x I = g x

      l : (x : A)(i j : 𝕀) → 𝕀₂ i j → k x i == k x j
      l x O O _ = refl
      l x O I _ = e x
      l x I O _ = symm (e x)
      l x I I _ = refl

      m : ty 𝕀₂ → (x : A) → B x
      m z x = elim 𝕀₂ (λ _ → B x) (k x) (λ {i} {j} _ → l x i j ⊤i) z

  -- Functions of two quotiented arguments (uses funext)
  lift₂ :
    {l l' m m' : Level}
    {A : Set l}
    {R : A → A → Prop m}
    {B : Set l'}
    {S : B → B → Prop m'}
    {n : Level}
    {C : Set n}
    (f : A → B → C)
    (_ : ∀ {x x' y } → R x x' → f x y == f x' y )
    (_ : ∀ {x y  y'} → S y y' → f x y == f x  y')
    → -------------------------------------------
    ty R → ty S → C
  lift₂ {S = S} f e₁ e₂ =
    lift
      (λ x → lift (λ y → f x y) e₂)
      (λ {x} {x'} r →
      funext (ind S
        (λ z → lift (λ y → f x y) e₂ z == lift (λ y → f x' y) e₂ z)
        (λ _ → e₁ r)))

  ind₂ :
    {l l' m m' : Level}
    {A : Set l}
    (R : A → A → Prop m)
    {B : Set l'}
    (S : B → B → Prop m')
    {n : Level}
    (P : ty R → ty S → Prop n)
    (f : ∀ x y → P (mk R x) (mk S y))
    → -------------------------------
    ∀ r s → P r s
  ind₂ R S P f =
    ind R (λ r → ∀ s → P r s) (λ x →
    ind S (P (mk R x)) (f x))

-- end module quot ---------------------------------------------------

-- Notation for quotients
infix 6 _/_ [_]/_
_/_ : {l m : Level}(A : Set l)(R : A → A → Prop m) → Set l
A / R = quot.ty R

[_]/_ : {l m : Level}{A : Set l} → A → (R : A → A → Prop m) → A / R
[ x ]/ R = quot.mk R x

-- Effectiveness of quotient by an equivalence relation
module quot-eff
  {l      : Level}
  {A      : Set l}
  (R      : A → A → Prop l)
  (Rrefl  : ∀{x y} → x == y → R x y)
  (Rsymm  : ∀{x y} → R x y → R y x)
  (Rtrans : ∀{x y z} → R y z → R x y → R x z)
  where
  -- Effectiveness property
  prop : {x y : A} → [ x ]/ R == [ y ]/ R → R x y
  prop p  = r p
    where
    f : ∀{x x' y} → R x x' → R x y == R x' y
    f p = propext -- Propositional Extensionality used here
      (∧i (λ q → Rtrans q (Rsymm p)) (λ q → Rtrans q p))

    g : ∀{x y y'} → R y y' → R x y == R x y'
    g p = propext -- Propositional Extensionality used here
      (∧i (λ q → Rtrans p q) (λ q → Rtrans (Rsymm p) q))

    R' : A / R  → A / R → Prop l
    R' = quot.lift₂ R f g

    r : {z z' : A / R} → z == z' → R' z z'
    r {z} refl =
      quot.ind R (λ z → R' z z) (λ _ → Rrefl refl) z

----------------------------------------------------------------------
-- Function Extensionality, derived from quotients
----------------------------------------------------------------------
funext :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  {f g : (x : A) → B x}
  (_ : ∀ x → f x == g x)
  → --------------------
  f == g
funext = quot.funext

funexp :
  {l m : Level}
  {A : Prop l}
  {B : A → Set m}
  {f g : (x : A) → B x}
  (_ : ∀ x → f x == g x)
  → ---------------------
  f == g
funexp {A = A} {B} {f} {g} e = ap f=g (eq O=I {x = O} {I} ⊤i)
  where
  open quot
  data 𝕀 : Set where
    O : 𝕀
    I : 𝕀

  O=I : 𝕀 → 𝕀 → Prop
  O=I _ _ = ⊤

  fg : (x : A) → 𝕀 → B x
  fg x O = f x
  fg x I = g x

  h : (x : A)(i j : 𝕀) → O=I i j → fg x i == fg x j
  h x O O _ = refl
  h x O I _ = e x
  h x I O _ = symm (e x)
  h x I I _ = refl

  f=g : ty O=I → (x : A) → B x
  f=g z x =
    elim O=I (λ _ → B x) (fg x) (λ {i} {j} _ → h x i j ⊤i) z

heq-funext :
  {l m : Level}
  {A A' : Set l}
  {B : A → Set m}
  {B' : A' → Set m}
  {f : (x : A) → B x}
  {f' : (x : A') → B' x}
  (_ : A == A')
  (_ : ∀{x x'} → x === x' → f x === f' x')
  → --------------------------------------
  f === f'
heq-funext refl e with funext (λ x → (===typ (e{x}{x} refl)))
... | refl = funext λ x → e{x}{x} refl

heq-funexp :
  {l m : Level}
  {A : Prop l}
  {B C : Set m}
  {f : A → B}
  {g : A → C}
  (_ : B == C)
  (_ : ∀ x → f x === g x)
  → ---------------------
  f === g
heq-funexp refl e' = funexp e'

heq-funexp' :
  {l m : Level}
  {A B : Prop l}
  {C : Set m}
  {f : A → C}
  {g : B → C}
  (_ : A == B)
  (_ : ∀ x y → f x === g y)
  → -----------------------
  f === g
heq-funexp' refl e = funexp λ x → e x x


--  Function extensionality with implicit arguments
implicit-funext :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  {f g : {x : A} → B x}
  (_ : ∀ x → f {x} == g {x})
  → ------------------------------
  (λ{x} → f {x}) == (λ{x} → g {x})
implicit-funext {A = A} {B} {f} {g} e =
  ap impl (funext {f = λ x → f{x}} {g = λ x → g{x}} e)
  where
  impl : ((x : A) → B x) → {x : A} → B x
  impl f {x} = f x

--  Function extensionality with implicit arguments (Prop)
implicit-funexp :
  {l m : Level}
  {A : Prop l}
  {B : A → Set m}
  {f g : {x : A} → B x}
  (_ : ∀ x → f {x} == g {x})
  → ------------------------------
  (λ{x} → f {x}) == (λ{x} → g {x})
implicit-funexp {A = A} {B} {f} {g} e =
  ap impl (funexp {f = λ x → f{x}} {g = λ x → g{x}} e)
  where
  impl : ((x : A) → B x) → {x : A} → B x
  impl f {x} = f x

--  Function extensionality with implicit arguments
instance-funext :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  {f g : {{x : A}} → B x}
  (_ : ∀ x → f {{x}} == g {{x}})
  → --------------------------------------
  (λ{{x}} → f {{x}}) == (λ{{x}} → g {{x}})
instance-funext {A = A} {B} {f} {g} e =
  ap sett (funext {f = λ x → f{{x}}} {g = λ x → g{{x}}} e)
  where
  sett : ((x : A) → B x) → {{x : A}} → B x
  sett f {{x}} = f x

instance-funexp :
  {l m : Level}
  {A : Prop l}
  {B : A → Set m}
  {f g : {{x : A}} → B x}
  (_ : ∀ x → f {{x}} == g {{x}})
  → --------------------------------------
  (λ{{x}} → f {{x}}) == (λ{{x}} → g {{x}})
instance-funexp {A = A} {B} {f} {g} e =
  ap sett (funexp {f = λ x → f{{x}}} {g = λ x → g{{x}}} e)
  where
  sett : ((x : A) → B x) → {{x : A}} → B x
  sett f {{x}} = f x

----------------------------------------------------------------------
-- The Axiom of Unique Choice
----------------------------------------------------------------------
postulate
  A!C : {l : Level}{A : Set l} → (∃ x ∶ A , ∀(x' : A) → x == x') → A

-- Definite description
module _
  {l m : Level}
  (A : Set l)
  (P : A → Prop m)
  where
  private
    AP : Set (l ⊔ m)
    AP = set A P

    ∃!AP : ∃! A P → ∃ z ∶ AP , ∀(z' : AP) → z == z'
    ∃!AP (∃i x (∧i p q)) =
      ∃i (x ∣ p) λ{(x' ∣ p') → setext (q x' p')}

  the : {{∃! A P}} → A
  the {{u}} = el (A!C (∃!AP u))

  the-pf : {{_ : ∃! A P}} → P the
  the-pf {{u}} = pf (A!C (∃!AP u))

  the-uniq : {{_ : ∃! A P}}(x : A) → P x → the == x
  the-uniq {{∃i x' (∧i p' q)}} x p =
    let
      instance
        _ : ∃! A P
        _ = ∃i x' (∧i p' q)
    in
    proof
      the
    =[ symm (q the the-pf) ]
      x'
    =[ q x p ]
      x
    qed

  syntax the A (λ x → P) = the x ∶ A , P

-- Isomorphisms of sets
isIso :
  {l m : Level}
  {X : Set l}
  {Y : Set m}
  → --------------------
  (X → Y) → Prop (l ⊔ m)
isIso {l} {m} {X} {Y} f = ∃ g ∶ (Y → X), iso g
  module _ where
  iso : (Y → X) → Prop (l ⊔ m)
  iso g = (∀ x → g (f x) == x) ∧ ∀ y → f (g y) == y

module _
  {l m : Level}
  {X : Set l}
  {Y : Set m}
  (f : X → Y)
  {{u : isIso f}}
  where
  private
    v : ∃! (Y → X) (iso f)
    v = match u \ where
      (∃i g invg@(∧i _ r)) → ∃i g (∧i invg λ{g' (∧i l' _) → funext λ y →
        proof
          g y
        =[ symm (l' (g y)) ]
          g' (f (g y))
        =[ ap g' (r y) ]
          g' y
        qed})

  _⁻¹ : Y → X
  _⁻¹ = the (Y → X) (iso f) {{v}}

  linv : ∀ x → _⁻¹ (f x) == x
  linv = ∧e₁ (the-pf (Y → X) (iso f) {{v}})

  rinv : ∀ y → f (_⁻¹ y) == y
  rinv = ∧e₂ (the-pf (Y → X) (iso f) {{v}})

-- Bijections are isomorphisms
bijectionIsIso :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (f : A → B)
  (_ : bijection f)
  → -----------------
  isIso f
bijectionIsIso {A = A} {B} f bij = ∃i finv (∧i lfinv rfinv)
  where
  instance
    ∃!x,fx=y :
      {y : B}
      → -----------------
      ∃! x ∶ A , f x == y
    ∃!x,fx=y {y} =
      match bij λ{(∧i m e) →
      match (e y) λ{(∃i x refl) →
      ∃i x (∧i refl (λ _ e → symm (m e)))}}

  finv : B → A
  finv y = the x ∶ A , (f x == y)

  lfinv : ∀ x → finv (f x) == x
  lfinv x = the-uniq A (λ x' → f x' == f x) x refl

  rfinv : ∀ y → f (finv y) == y
  rfinv y = the-pf A (λ x → f x == y)

-- Transport along a propositional equality between types
coe :
  {l : Level}
  {A B : Set l}
  → ------------
  A == B → A → B
coe {A = A} {B} e x = the B (_=== x) {{coe! e}}
  module _ where
  coe! : A == B → ∃! y ∶ B , y === x
  coe! refl = ∃i x (∧i refl λ _ p → symm p)

coerefl :
  {l : Level}
  {A : Set l}
  (x : A)
  → -------------
  coe refl x == x
coerefl x = the-pf _ (_=== x) {{coe! refl x refl}}

coe=== :
  {l : Level}
  {A A' : Set l}
  (e : A == A')
  (x : A)
  → -------------
  coe e x === x
coe=== refl x = coerefl x

coe⁻¹ :
  {l : Level}
  {A B : Set l}
  → ------------
  A == B → B → A
coe⁻¹ e = coe (symm e)

coe⁻¹coe :
  {l : Level}
  {A B : Set l}
  {e : A == B}
  (x : A)
  → --------------------
  coe⁻¹ e (coe e x) == x
coe⁻¹coe {e = refl} x =
  proof
    coe refl (coe refl x)
  =[ coerefl _ ]
    coe refl x
  =[ coerefl _ ]
    x
  qed

coecoe⁻¹ :
  {l : Level}
  {A B : Set l}
  {e : A == B}
  (y : B)
  → --------------------
  coe e (coe⁻¹ e y) == y
coecoe⁻¹ {e = refl} y =
  proof
    coe refl (coe refl y)
  =[ coerefl _ ]
    coe refl y
  =[ coerefl _ ]
    y
  qed

coe=id :
  {l : Level}
  {A A' : Set l}
  (e : A == A')
  → ------------------
  coe e === id {A = A}
coe=id refl = funext λ x → coerefl x

∘coe :
  {l m : Level}
  {A A' : Set l}
  {B : Set m}
  (e : A == A')
  (f : A' → B)
  → --------------
  f ∘ coe e === f
∘coe refl f = ap (f ∘_) (coe=id refl)

-- Surjections are effective epimorphisms
module EffEpi
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (q : B → A)
  (surj : surjection q)
  {n : Level}
  {C : Set n}
  (f : B → C)
  (p : ∀ y y' → q y == q y' → f y == f y')
  where
  -- Given the assumptions, there is a unique function lift : A → C
  -- such that lift ∘ q == f
  private
    P : A → C → Prop (l ⊔ m ⊔ n)
    P x z = ∃ y ∶ B , (q y == x ∧ z == f y)

    u : (x : A) → ∃! z ∶ C , P x z
    u x with surj x
    ... | ∃i y refl =
      ∃i (f y) (∧i (∃i y (∧i refl refl))
      λ{ _ (∃i y' (∧i qy'=qy refl)) → p y y' (symm qy'=qy)})

  lift : A → C
  lift x = the C (P x) {{u x}}

  comp : ∀ y → lift (q y) == f y
  comp y =
    match (the-pf C (P (q y)) {{u (q y)}}) \ where
      (∃i y' (∧i qy'=qy e)) →
        proof
          (lift ∘ q) y
        =[ e ]
          f y'
        =[ p y' y qy'=qy ]
          f y
        qed

  uniq :
    (g : A → C)
    (_ : g ∘ q == f)
    (x : A)
    → --------------
    lift x == g x
  uniq g gq=f x =
    match (surj x) \ where
      (∃i y refl) →
        the-uniq C (P x) {{u x}} (g x)
        (∃i y (∧i refl (ap (case y) gq=f)))
