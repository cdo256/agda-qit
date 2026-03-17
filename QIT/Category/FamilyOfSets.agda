{-# OPTIONS --type-in-type #-}
module QIT.Category.FamilyOfSets where

-- A simpler variant of FamilyOfSetoids where the base is a Set (not a Setoid)
-- and fibers are plain Sets. This eliminates the need for reindexing coherence laws.

open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid
open import QIT.Category.Base
open import QIT.Relation.Binary using (IsEquivalence)

-- A family of sets indexed by a base set
record Fam (ℓU ℓT : Level) : Set (lsuc (ℓU ⊔ ℓT)) where
  constructor fam
  field
    U : Set ℓU           -- Base set
    T : U → Set ℓT       -- Fiber over each element of U

open Fam

module FamCat {ℓU ℓT : Level} where
  private
    Fam' = Fam ℓU ℓT

  -- A morphism between families: a map on bases plus a fiber map
  record Hom (A B : Fam') : Set (ℓU ⊔ ℓT) where
    constructor fhom
    field
      map : U A → U B                              -- Base map
      transport : (x : U A) → T A x → T B (map x)  -- Fiber map

  open Hom

  -- Morphism equality: pointwise equality on both base and fibers
  record _≋_ {A B : Fam'} (f g : Hom A B) : Set (ℓU ⊔ ℓT) where
    constructor feq
    field
      ≈map : ∀ (x : U A) → map f x ≡ map g x
      ≈transport : ∀ (x : U A) (y : T A x)
                 → ≡.subst (T B) (≈map x) (transport f x y)
                 ≡ transport g x y

  -- Identity morphism
  fam-id : {A : Fam'} → Hom A A
  fam-id = fhom (λ x → x) (λ _ ax → ax)

  -- Composition of morphisms
  comp : {A B C : Fam'} → Hom B C → Hom A B → Hom A C
  comp g f = fhom
    (λ x → map g (map f x))
    (λ x ax → transport g (map f x) (transport f x ax))

  -- Helper lemmas for substitution
  private
    subst² : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') {x y z : A}
           → (p : x ≡ y) (q : y ≡ z) (u : P x)
           → ≡.subst P q (≡.subst P p u) ≡ ≡.subst P (≡.trans p q) u
    subst² P ≡.refl ≡.refl u = ≡.refl

    subst-cong : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (P : B → Set ℓ'')
               → {x y : A} (p : x ≡ y) (u : P (f x))
               → ≡.subst P (≡.cong f p) u ≡ ≡.subst (λ a → P (f a)) p u
    subst-cong f P ≡.refl u = ≡.refl



  -- Equivalence relation on morphisms
  ≋-refl : ∀ {A B} {f : Hom A B} → f ≋ f
  ≋-refl {A} {B} {f} =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map f x ≡ map f x
    r _ = ≡.refl
    r̂ : ∀ (x : U A) (y : T A x)
                → ≡.subst (T B) (r x) (transport f x y)
                ≡ transport f x y
    r̂ x ax = refl

  ≋-sym : ∀ {A B} {f g : Hom A B} → f ≋ g → g ≋ f
  ≋-sym {A} {B} {f} {g} (feq p p̂) =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map g x ≡ map f x
    r x = sym (p x)
    r̂ : ∀ (x : U A) (y : T A x)
                → ≡.subst (T B) (r x) (transport g x y)
                ≡ transport f x y
    r̂ x y =
      subst (T B) (r x) (transport g x y)
        ≡⟨ cong (subst (T B) (r x)) (sym (p̂ x y)) ⟩
      subst (T B) (r x) (subst (T B) (p x) (transport f x y))
        ≡⟨ subst² (T B) (p x) (r x) (transport f x y) ⟩
      subst (T B) (trans (p x) (r x)) (transport f x y)
        ≡⟨ cong (λ q → subst (T B) q (transport f x y))
                 (≡.trans-symʳ (p x)) ⟩
      subst (T B) refl (transport f x y)
        ≡⟨ refl ⟩
      transport f x y ∎


  ≋-trans : ∀ {A B} {f g h : Hom A B} → f ≋ g → g ≋ h → f ≋ h
  ≋-trans {A} {B} {f} {g} {h} (feq p p̂) (feq q q̂) =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map f x ≡ map h x
    r x = trans (p x) (q x)
    r̂ : ∀ (x : U A) (y : T A x)
                → ≡.subst (T B) (r x) (transport f x y)
                ≡ transport h x y
    r̂ x y =
      subst (T B) (r x) (transport f x y)
        ≡⟨ sym (subst² (T B) (p x) (q x) (transport f x y)) ⟩
      subst (T B) (q x) (subst (T B) (p x) (transport f x y))
        ≡⟨ cong (subst (T B) (q x)) (p̂ x y) ⟩
      subst (T B) (q x) (transport g x y)
        ≡⟨ q̂ x y ⟩
      transport h x y ∎



  -- Composition respects morphism equality
  comp-resp-≋ : {A B C : Fam'} {f h : Hom B C} {g i : Hom A B} →
    f ≋ h → g ≋ i → comp f g ≋ comp h i
  comp-resp-≋ {A} {B} {C} {f} {h} {g} {i} (feq p p̂) (feq q q̂) =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map f (map g x) ≡ map h (map i x)
    r x = trans (cong (map f) (q x)) (p (map i x))

    -- Helper: after substituting along q x, we can apply p̂
    step : ∀ x y → subst (λ a → T C (map f a)) (q x) (transport f (map g x) (transport g x y))
                 ≡ transport f (map i x) (transport i x y)
    step x y with q x | q̂ x y
    ... | refl | refl = refl

    r̂ : ∀ (x : U A) (y : T A x)
                → ≡.subst (T C) (r x) (transport f (map g x) (transport g x y))
                ≡ transport h (map i x) (transport i x y)
    r̂ x y =
      subst (T C) (r x) (transport f (map g x) (transport g x y))
        ≡⟨ sym (subst² (T C) (cong (map f) (q x)) (p (map i x))
                  (transport f (map g x) (transport g x y))) ⟩
      subst (T C) (p (map i x)) (subst (T C) (cong (map f) (q x))
        (transport f (map g x) (transport g x y)))
        ≡⟨ cong (subst (T C) (p (map i x)))
                (subst-cong (map f) (T C) (q x) (transport f (map g x) (transport g x y))) ⟩
      subst (T C) (p (map i x)) (subst (λ a → T C (map f a)) (q x)
        (transport f (map g x) (transport g x y)))
        ≡⟨ cong (subst (T C) (p (map i x))) (step x y) ⟩
      subst (T C) (p (map i x)) (transport f (map i x) (transport i x y))
        ≡⟨ p̂ (map i x) (transport i x y) ⟩
      transport h (map i x) (transport i x y) ∎

  -- The category of families of sets
  Cat : Category (lsuc (ℓU ⊔ ℓT)) (ℓU ⊔ ℓT) (ℓU ⊔ ℓT)
  Cat = record
    { Obj = Fam'
    ; _⇒_ = Hom
    ; _≈_ = λ f g → ∥ f ≋ g ∥
    ; id = fam-id
    ; _∘_ = comp
    ; assoc = λ {A B C D f g h} → assoc {A} {B} {C} {D} {f} {g} {h}
    ; sym-assoc = λ {A B C D f g h} → ∣ ≋-sym (untrunc (assoc {A} {B} {C} {D} {f} {g} {h})) ∣
    ; identityˡ = λ {A B f} → identityˡ {A} {B} {f}
    ; identityʳ = λ {A B f} → identityʳ {A} {B} {f}
    ; identity² = λ {A} → identity² {A}
    ; equiv = record
      { refl = ∣ ≋-refl ∣
      ; sym = λ { ≡.refl → ≡.refl }
      ; trans = λ { ≡.refl ≡.refl → ≡.refl }
      }
    ; ∘-resp-≈ = λ { ≡.refl ≡.refl → ≡.refl }
    }
    where
    open ≡.≡-Reasoning
    open ≡
    untrunc : ∀ {ℓ} {A : Set ℓ} → ∥ A ∥ → A
    untrunc ∣ x ∣ = x

    -- Associativity of composition
    assoc : {A B C D : Fam'} {f : Hom A B} {g : Hom B C} {h : Hom C D} →
      ∥ comp (comp h g) f ≋ comp h (comp g f) ∥
    assoc {A} {B} {C} {D} {f} {g} {h} = ∣ feq (λ x → refl) (λ x y → refl) ∣

    -- Left identity
    identityˡ : {A B : Fam'} {f : Hom A B} → ∥ comp fam-id f ≋ f ∥
    identityˡ {A} {B} {f} = ∣ feq (λ x → refl) (λ x y → refl) ∣

    -- Right identity
    identityʳ : {A B : Fam'} {f : Hom A B} → ∥ comp f fam-id ≋ f ∥
    identityʳ {A} {B} {f} = ∣ feq (λ x → refl) (λ x y → refl) ∣

    -- Identity composition
    identity² : {A : Fam'} → ∥ comp fam-id fam-id ≋ fam-id {A} ∥
    identity² {A} = ∣ feq (λ x → refl) (λ x y → refl) ∣

open FamCat public hiding (Cat)

-- Export the category constructor
FamilyOfSets : ∀ ℓU ℓT → Category (lsuc (ℓU ⊔ ℓT)) (ℓU ⊔ ℓT) (ℓU ⊔ ℓT)
FamilyOfSets ℓU ℓT = FamCat.Cat {ℓU} {ℓT}
