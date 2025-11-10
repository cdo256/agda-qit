{-#  OPTIONS --prop --rewriting --show-irrelevant #-}

module WeaklyInitialSetsOfCovers where

open import IndexedContainersAndEquationalSystems public

----------------------------------------------------------------------
-- Families of sets
----------------------------------------------------------------------
record Fam (l : Level) : Set (lsuc l) where
  constructor mkFam
  field
    base  : Set l
    fiber : base → Set l

open Fam public

----------------------------------------------------------------------
-- WISC property of a family W for a set A
----------------------------------------------------------------------
wisc : {l : Level} → Set l → Fam l → Prop (lsuc l)
wisc {l} A W =
  (E : Set l)
  (q : E → A)
  (_ : surjection q)
  → --------------------
  ∃ c ∶ base W ,
  ∃ f ∶ (fiber W c → E),
    surjection (q ∘ f)

----------------------------------------------------------------------
-- A weak form of choice derived from the wisc property (Lemma 4.3)
----------------------------------------------------------------------
wAC :
  {l : Level}
  {A : Set l}
  (W : Fam l)
  (_ : wisc A W)
  (B : A → Set l)
  (P : (x : A) → B x → Prop l)
  (_ : ∀ x → ∃ (B x) (P x))
  → ------------------------------------
  ∃ c ∶ base W ,
  ∃ p ∶ (fiber W c → A),
  ∃ q ∶ ((z : fiber W c) → B (p z)),
    (surjection p ∧ ∀ z → P (p z) (q z))
wAC {l} {A} W w B P e = wac
  where
  C : Set l
  C = set (x , y) ∶ (∑ A B), P x y

  p' : C → A
  p' ((x , _) ∣ _) = x

  surjectionp' : surjection p'
  surjectionp' x with e x
  ... | ∃i y u = ∃i ((x , y) ∣ u) refl

  q' : (z : C) → B (p' z)
  q' ((_ , y) ∣ _) = y

  r : ∀ z → P (p' z) (q' z)
  r ((_ , _) ∣ p) = p

  wac : ∃ c ∶ base W ,
      ∃ p ∶ (fiber W c → A),
      ∃ q ∶ ((z : fiber W c) → B (p z)),
        (surjection p ∧ ∀ z → P (p z) (q z))
  wac with w C p' surjectionp'
  ... | ∃i c (∃i k u) =
    ∃i c (
    ∃i (p' ∘ k) (
    ∃i (q' ∘ k) (
    ∧i u λ z → r (k z))))

-- A useful variant of wAC
oldsklWISC :
  {l : Level}
  {A : Set l}
  (W : Fam l)
  (_ : wisc A W)
  {B E : Set l}
  (f : A → B)
  (q : E → B)
  (_ : surjection q)
  → --------------------------------
  ∃ c  ∶ base W ,
  ∃ p  ∶ (fiber W c → A),
  ∃ f' ∶ (fiber W c → E),
    (surjection p ∧ q ∘ f' == f ∘ p)
oldsklWISC {l} {A} W Wwisc {B} {E} f q surjq = match wac (λ {
    (∃i c (∃i g (∃i g' (∧i gsurj eq)))) →
     ∃i c (∃i g (∃i g' (∧i gsurj (funext eq)))
    )
  })
  where
  P : A → E → Prop l
  P pz f'z = q f'z == f pz

  Ptotal : (x : A) → ∃ E (P x)
  Ptotal x = surjq (f x)

  wac = wAC W Wwisc (λ _ → E) P Ptotal

----------------------------------------------------------------------
-- The IWISC Axiom (Definition 4.1)
----------------------------------------------------------------------
postulate
  IWISC :
    {l : Level}
    (F : Fam l)
    → ------------------------------------
    ∃ W ∶ Fam l , ∀ c → wisc (fiber F c) W
