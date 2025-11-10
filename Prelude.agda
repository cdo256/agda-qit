module Prelude where

open import Agda.Primitive public

----------------------------------------------------------------------
-- Coercions between Set and Prop universes
----------------------------------------------------------------------
record LiftSet {l l' : Level} (A : Set l) : Set (l ⊔ l') where
  constructor ↑set
  field ↓set : A

open LiftSet public

record LiftProp {l l' : Level} (P : Prop l) : Set (l ⊔ l') where
  constructor ↑prop
  field ↓prop : P

open LiftProp public

----------------------------------------------------------------------
-- Identity function
----------------------------------------------------------------------
id :
 {l : Level}
 {A : Set l}
 → ---------
 A → A
id x = x

----------------------------------------------------------------------
-- Constant function
----------------------------------------------------------------------
K :
 {l m : Level}
 {A : Set l}
 (B : Set m)
 → -----------
 A → B → A
K _ x _ = x

----------------------------------------------------------------------
-- Composition
----------------------------------------------------------------------
infixr 5 _∘_
_∘_ :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : (x : A) → B x → Set n}
  (g : {x : A}(y : B x) → C x y)
  (f : (x : A) → B x)
  → ----------------------------
  (x : A) → C x (f x)
(g ∘ f) x = g (f x)

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------
data 𝟘 {l : Level} : Set l where

𝟘e :
  {l m : Level}
  {A : 𝟘 {l} → Set m}
  → -----------------
  ∀ x → A x
𝟘e ()

----------------------------------------------------------------------
-- Booleans
----------------------------------------------------------------------
data 𝔹 : Set where
  true false : 𝔹

{-# BUILTIN BOOL  𝔹  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

----------------------------------------------------------------------
-- True
----------------------------------------------------------------------
data ⊤ {l : Level} : Prop l where
  ⊤i : ⊤

----------------------------------------------------------------------
-- False
----------------------------------------------------------------------
data ⊥ {l : Level} : Prop l where

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------
infix 3 ¬_
¬_ : {l : Level} → Prop l → Prop l
¬_ {l} P = P → ⊥ {l}

----------------------------------------------------------------------
-- Heterogeneous propositional equality
----------------------------------------------------------------------
infix 4 _===_
data _===_
  {l : Level}
  {A : Set l}
  : --------------------------------
  {B : Set l}(x : A)(y : B) → Prop l
  where
  instance refl : {x : A} → x === x

{-# BUILTIN REWRITE _===_ #-}

===irrel :
 {l : Level}
 {P Q : Prop l}
 {p : P}
 {q : Q}
 → ----------------------------------
 P === Q → ↑prop{l}{l} p === ↑prop  q
===irrel refl = refl

===typ :
  {l : Level}
  {A B : Set l}
  {x : A}
  {y : B}
  → -------------
  x === y → A === B
===typ refl = refl

coeₚ : {l : Level}{P Q : Prop l} → P === Q → P → Q
coeₚ refl x = x

coeₚ⁻¹ : {l : Level}{P Q : Prop l} → P === Q → Q → P
coeₚ⁻¹ refl x = x

ap :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  (f : (x : A) → B x)
  {x y : A}
  (_ : x === y)
  → -----------------
  f x === f y
ap _ refl = refl

ap₂ :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : (x : A) → B x → Set n}
  (f : (x : A)(y : B x) → C x y)
  {x x' : A}
  (_ : x === x')
  {y : B x}
  {y' : B x'}
  (_ : y === y')
  → ----------------------------
  f x y === f x' y'
ap₂ _ refl refl = refl

trans :
  {l : Level}
  {A B C : Set l}
  {x : A}
  {y : B}
  {z : C}
  (q : y === z)
  (p : x === y)
  → ----------
  x === z
trans refl p = p

symm :
  {l : Level}
  {A B : Set l}
  {x : A}
  {y : B}
  (p : x === y)
  → ---------
  y === x
symm refl = refl

infix  1 proof_
proof_ :
  {l : Level}
  {A B : Set l}
  {x : A}
  {y : B}
  → -------------
  x === y → x === y
proof p = p

infixr 2 _=[_]_
_=[_]_ :
  {l : Level}
  {A B C : Set l}
  (x : A)
  {y : B}
  {z : C}
  → ----------------------
  x === y → y === z → x === z
_ =[ p ] q = trans q p

infix  3 _qed
_qed :
  {l : Level}
  {A : Set l}
  (x : A)
  → ---------
  x === x
_ qed = refl

substp :
  {l m : Level}
  {A  A' : Set l}
  {P : A → Prop m}
  {P' : A' → Prop m}
  (_ : P === P')
  {x : A}
  {x' : A'}
  (_ : x === x')
  → ----------------
  P x → P' x'
substp e e' p with ===typ e'
substp refl refl p | refl = p

substp₂ :
  {l m n : Level}
  {A A' : Set l}
  {B B' : Set m}
  {P : A → B → Prop n}
  {P' : A' → B' → Prop n}
  (_ : P === P')
  {x : A}
  {x' : A'}
  {y : B}
  {y' : B'}
  (_ : x === x')
  (_ : y === y')
  → ---------------------
  P x y → P' x' y'
substp₂ e e' e'' p with ===typ e' | ===typ e''
substp₂ refl refl refl p | refl | refl = p

----------------------------------------------------------------------
-- Homogeneous propositional equality
----------------------------------------------------------------------
infix 4 _==_
_==_ : {l : Level}{A : Set l}(x y : A) → Prop l
_==_ = _===_

----------------------------------------------------------------------
-- Conjunction
----------------------------------------------------------------------
infixr 3 _∧_
data _∧_ {l m : Level}(P : Prop l)(Q : Prop m) : Prop (l ⊔ m) where
  ∧i : P → Q → P ∧ Q

∧e₁ :
  {l m : Level}
  {P : Prop l}
  {Q : Prop m}
  → -----------
  P ∧ Q → P
∧e₁ (∧i p _) = p

∧e₂ :
  {l m : Level}
  {P : Prop l}
  {Q : Prop m}
  → -----------
  P ∧ Q → Q
∧e₂ (∧i _ q) = q

----------------------------------------------------------------------
-- Bimplication
----------------------------------------------------------------------
infix 3 _↔_
_↔_ : {l : Level} → Prop l → Prop l → Prop l
P ↔ Q = (P → Q) ∧ (Q → P)

----------------------------------------------------------------------
-- Propositional truncation
----------------------------------------------------------------------
data Inhabited {l : Level}(A : Set l) : Prop l where
  inhab : (x : A) → Inhabited A

----------------------------------------------------------------------
-- Exists
----------------------------------------------------------------------
infix  1 ∃
data ∃ {l m : Level}(A : Set l)(P : A → Prop m) : Prop (l ⊔ m) where
  ∃i : (x : A)(p : P x) → ∃ A P

syntax ∃ A (λ x → P) = ∃ x ∶ A , P

----------------------------------------------------------------------
-- Unique existence
----------------------------------------------------------------------
infix  1 ∃!
∃! : {l m : Level}(A : Set l)(P : A → Prop m) → Prop (l ⊔ m)
∃! A P = ∃ x ∶ A , (P x ∧ ∀(x' : A) → P x' → x == x')

syntax ∃! A (λ x → P) = ∃! x ∶ A , P

----------------------------------------------------------------------
-- Dependent conjunction
----------------------------------------------------------------------
infix  1 ⋀
data ⋀ {l m : Level}(P : Prop l)(Q : P → Prop m) : Prop (l ⊔ m) where
  ⋀i : (x : P)(p : Q x) → ⋀ P Q

syntax ⋀ P (λ p → Q) = ⋀ p ∶ P , Q

⋀e₁ :
  {l m : Level}
  {P : Prop l}
  {Q : P → Prop m}
  → --------------
  ⋀ P Q → P
⋀e₁ (⋀i p _) = p

⋀e₂ :
  {l m : Level}
  {P : Prop l}
  {Q : P → Prop m}
  (⋀pq : ⋀ P Q)
  → --------------
  Q (⋀e₁ ⋀pq)
⋀e₂ (⋀i _ q) = q

----------------------------------------------------------------------
-- Disjunction
----------------------------------------------------------------------
infixr 1 _∨_
data _∨_ {l m : Level}(P : Prop l)(Q : Prop m) : Prop (l ⊔ m) where
  ∨i₁ : P → P ∨ Q
  ∨i₂ : Q → P ∨ Q

----------------------------------------------------------------------
-- Case expressions
----------------------------------------------------------------------
case :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  (x : A)
  (f : (x : A) → B x)
  → -----------------
  B x
case x f  = f x

casep :
  {l m : Level}
  {A : Set l}
  {P : A → Prop m}
  (x : A)
  (p : (x : A) → P x)
  → -----------------
  P x
casep x p  = p x

match :
  {l m : Level}
  {P : Prop l}
  {Q : P → Prop m}
  (p : P)
  (q : ∀ p → Q p)
  → --------------
  Q p
match p q  = q p

----------------------------------------------------------------------
-- Comprehension
----------------------------------------------------------------------
infixl 4 _∣_
record set
  {l m : Level}
  (A : Set l)
  (P : A → Prop m)
  : --------------
  Set (l ⊔ m)
  where
  constructor _∣_
  field
    el : A
    pf : P el
open set public

syntax set A (λ x → P) = set x ∶ A , P

setext :
  {l m : Level}
  {A : Set l}
  {P : A → Prop m}
  {z z' : set A P}
  (_ : el z == el z')
  → -----------------
  z == z'
setext {z = _ ∣ _} {_ ∣ _} refl = refl

----------------------------------------------------------------------
-- Injections
----------------------------------------------------------------------
injection :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (f : A → B)
  → -----------
  Prop (l ⊔ m)
injection f = ∀{x x'} → f x == f x' → x == x'

----------------------------------------------------------------------
-- Surjective functions
----------------------------------------------------------------------
surjection :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (q : B → A)
  → -----------
  Prop (l ⊔ m)

surjection q = ∀ x → ∃ y ∶ _ , q y == x

----------------------------------------------------------------------
-- Bijections
----------------------------------------------------------------------
bijection :
  {l m : Level}
  {A : Set l}
  {B : Set m}
  (f : A → B)
  → ----------
  Prop (l ⊔ m)
bijection f = injection f ∧ surjection f

----------------------------------------------------------------------
-- Dependent functions
----------------------------------------------------------------------
∏ :
  {l m : Level}
  (A : Set l)
  (B : A → Set m)
  → --------------
  Set (l ⊔ m)
∏ A B = (x : A) → B x

syntax ∏ A (λ x → B) = ∏ x ∶ A , B

----------------------------------------------------------------------
-- Dependent product
----------------------------------------------------------------------
infixr 4 _,_
record ∑ {l m : Level}(A : Set l)(B : A → Set m) : Set(l ⊔ m) where
  constructor _,_
  field
    fst : A
    snd : B fst

{-# BUILTIN SIGMA ∑ #-}

open ∑ public

infix 2 ∑-syntax
∑-syntax : {l m : Level}(A : Set l) → (A → Set m) → Set (l ⊔ m)
∑-syntax = ∑
syntax ∑-syntax A (λ x → B) = ∑ x ∶ A , B

pair :
  {l m : Level}
  {A : Set l}
  (B : A → Set m)
  (x : A)
  (_ : B x)
  → -------------
  ∑ A B
pair _ x y = (x , y)

∑ext :
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  {x x' : A}
  {y : B x}
  {y' : B x'}
  (_ : x == x')
  (_ : y === y')
  → -----------------------
  pair B x y == pair B x' y'
∑ext refl refl = refl

∑heq₁ :
  {l m : Level}
  {A A' : Set l}
  {B : A → Set m}
  {B' : A' → Set m}
  {x : A}
  {x' : A'}
  {y : B x}
  {y' : B' x'}
  (_ : A == A')
  (_ : B === B')
  (_ : pair B x y === pair B' x' y')
  → --------------------------------
  x === x'
∑heq₁ refl refl refl = refl

∑heq₂ :
  {l m : Level}
  {A A' : Set l}
  {B : A → Set m}
  {B' : A' → Set m}
  {x : A}
  {x' : A'}
  {y : B x}
  {y' : B' x'}
  (_ : A == A')
  (_ : B === B')
  (_ : pair B x y === pair B' x' y')
  → --------------------------------
  y === y'
∑heq₂ refl refl refl = refl

record ∑ₚ {l m : Level}(P : Prop l)(B : P → Set m) : Set(l ⊔ m) where
  constructor _,_
  field
    fst : P
    snd : B fst

open ∑ₚ public

infix 2 ∑ₚ-syntax
∑ₚ-syntax : {l m : Level}(P : Prop l) → (P → Set m) → Set (l ⊔ m)
∑ₚ-syntax = ∑ₚ
syntax ∑ₚ-syntax P (λ p → B) = ∑ₚ p ∶ P , B

pairₚ :
  {l m : Level}
  {P : Prop l}
  (B : P → Set m)
  (x : P)
  (_ : B x)
  → -------------
  ∑ₚ P B
pairₚ _ x y = (x , y)

∑ₚheq :
  {l m : Level}
  {P P' : Prop l}
  {B : P → Set m}
  {B' : P' → Set m}
  {x : P}
  {x' : P'}
  {y : B x}
  {y' : B' x'}
  (_ : P == P')
  (_ : B === B')
  (_ : pairₚ B x y === pairₚ B' x' y')
  → ----------------------------------
  y === y'
∑ₚheq refl refl refl = refl

uncurry :
  {l m n : Level}
  {A : Set l}
  {B : A → Set m}
  {C : (a : A) → B a → Set n}
  (f : (a : A) (b : B a) → C a b)
  → -----------------------------
  (x : ∑ A B) → C (fst x) (snd x)
uncurry f (fst , snd) = f fst snd

----------------------------------------------------------------------
-- Cartesian product
----------------------------------------------------------------------
infixr 5 _×_
_×_ : {l m : Level} → Set l → Set m → Set (l ⊔ m)
A × B = ∑ A (λ _ → B)

----------------------------------------------------------------------
-- Unit type
----------------------------------------------------------------------
record 𝟙 : Set where
  instance constructor tt

{-# BUILTIN UNIT 𝟙 #-}

record Unit {l : Level} : Set l where
  instance constructor unit

----------------------------------------------------------------------
-- Disjoint union
----------------------------------------------------------------------
infixr 1 _+_
data _+_ {l m : Level}(A : Set l)(B : Set m) : Set (l ⊔ m) where
  ι₁ : (x : A) → A + B
  ι₂ : (y : B) → A + B

_+'_ :
  {l m n : Level}
  {X : Set l}
  (A : X → Set m)
  (B : X → Set n)
  (x : X)
  → -------------
  Set (m ⊔ n)
(A +' B) x = A x + B x

[_,_] :
  {l m n : Level}
  {A : Set l}
  {B : Set m}
  {C : A + B → Set n} →
  (f : (x : A) → C (ι₁ x))
  (g : (x : B) → C (ι₂ x))
  → ----------------------
  (x : A + B) → C x
[ f , g ] (ι₁ x) = f x
[ f , g ] (ι₂ y) = g y

----------------------------------------------------------------------
-- Natural number type
----------------------------------------------------------------------
data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
{-# BUILTIN NATURAL ℕ #-}

pattern _+1 n = suc n

infix 4 _≐_
_≐_ : ℕ → ℕ → 𝔹
zero ≐ zero     = true
zero ≐ (n +1)   = false
(m +1) ≐ zero   = false
(m +1) ≐ (n +1) = m ≐ n

decidableℕ : (m n : ℕ) → m == n ∨ ¬(m == n)
decidableℕ zero zero                         = ∨i₁ refl
decidableℕ zero (n +1)                       = ∨i₂ λ{()}
decidableℕ (m +1) zero                       = ∨i₂ λ{()}
decidableℕ (m +1) (n +1) with decidableℕ m n
...                      | ∨i₁ refl          = ∨i₁ refl
...                      | ∨i₂ p             = ∨i₂ λ{refl → p refl}

----------------------------------------------------------------------
-- Lists
----------------------------------------------------------------------
infixr 6 _∷_
data List {l : Level}(A : Set l) : Set l where
  []  : List A
  _∷_ : (x : A)(xs : List A) → List A

{-# BUILTIN LIST List #-}

----------------------------------------------------------------------
-- Kernels
----------------------------------------------------------------------
module _
  {l m : Level}
  {A : Set l}
  {B : A → Set m}
  (f : (x : A) → B x)
  where
  ker : Set (l ⊔ m)
  ker = set (x , x') ∶ A × A , (f x === f x')

  πker₁ : ker → A
  πker₁ ((x , _) ∣ _) = x

  πker₂ : ker → A
  πker₂ ((_ , x') ∣ _) = x'

  eqker : (z : ker) → f (πker₁ z) === f (πker₂ z)
  eqker ((_ , _) ∣ e) = e
