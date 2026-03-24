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
      transport : {x : U A} → T A x → T B (map x)  -- Fiber map

  open Hom

  -- Morphism equality: pointwise equality on both base and fibers
  record _≡ꟳ_ {A B : Fam'} (f g : Hom A B) : Prop (ℓU ⊔ ℓT) where
    constructor feq
    field
      ≡map : ∀ (x : U A) → map f x ≡ map g x
      ≡transport : ∀ {x : U A} (y : T A x)
                 → ≡.subst (T B) (≡map x) (transport f y)
                 ≡ transport g y

  -- Identity morphism
  fam-id : {A : Fam'} → Hom A A
  fam-id = fhom (λ x → x) (λ ax → ax)

  -- Composition of morphisms
  comp : {A B C : Fam'} → Hom B C → Hom A B → Hom A C
  comp g f = fhom
    (λ x → map g (map f x))
    (λ {x} ax → transport g (transport f ax))

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
  ≡ꟳ-refl : ∀ {A B} {f : Hom A B} → f ≡ꟳ f
  ≡ꟳ-refl {A} {B} {f} =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map f x ≡ map f x
    r _ = ≡.refl
    r̂ : ∀ {x : U A} (y : T A x)
                → ≡.subst (T B) (r x) (transport f y)
                ≡ transport f y
    r̂ ax = refl

  ≡ꟳ-sym : ∀ {A B} {f g : Hom A B} → f ≡ꟳ g → g ≡ꟳ f
  ≡ꟳ-sym {A} {B} {f} {g} (feq p p̂) =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map g x ≡ map f x
    r x = sym (p x)
    r̂ : ∀ {x : U A} (y : T A x)
      → ≡.subst (T B) (r x) (transport g y)
      ≡ transport f y
    r̂ {x} y =
      subst (T B) (r x) (transport g y)
        ≡⟨ cong (subst (T B) (r x)) (sym (p̂ y)) ⟩
      subst (T B) (r x) (subst (T B) (p x) (transport f y))
        ≡⟨ subst² (T B) (p x) (r x) (transport f y) ⟩
      subst (T B) (trans (p x) (r x)) (transport f y)
        ≡⟨ cong (λ q → subst (T B) q (transport f y))
                 (≡.trans-symʳ (p x)) ⟩
      subst (T B) refl (transport f y)
        ≡⟨ refl ⟩
      transport f y ∎

  ≡ꟳ-trans : ∀ {A B} {f g h : Hom A B} → f ≡ꟳ g → g ≡ꟳ h → f ≡ꟳ h
  ≡ꟳ-trans {A} {B} {f} {g} {h} (feq p p̂) (feq q q̂) =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map f x ≡ map h x
    r x = trans (p x) (q x)
    r̂ : ∀ {x : U A} (y : T A x)
                → ≡.subst (T B) (r x) (transport f y)
                ≡ transport h y
    r̂ {x} y =
      subst (T B) (r x) (transport f y)
        ≡⟨ sym (subst² (T B) (p x) (q x) (transport f y)) ⟩
      subst (T B) (q x) (subst (T B) (p x) (transport f y))
        ≡⟨ cong (subst (T B) (q x)) (p̂ y) ⟩
      subst (T B) (q x) (transport g y)
        ≡⟨ q̂ y ⟩
      transport h y ∎

  -- Composition respects morphism equality
  comp-resp-≡ꟳ : {A B C : Fam'} {f h : Hom B C} {g i : Hom A B} →
    f ≡ꟳ h → g ≡ꟳ i → comp f g ≡ꟳ comp h i
  comp-resp-≡ꟳ {A} {B} {C} {f} {h} {g} {i} (feq p p̂) (feq q q̂) =
    feq r r̂
    where
    open ≡.≡-Reasoning
    open ≡
    r : (x : U A) → map f (map g x) ≡ map h (map i x)
    r x = trans (cong (map f) (q x)) (p (map i x))

    -- Naturality of transport with respect to substitution
    -- We use subst eliminator by defining the motive properly
    transport-nat : ∀ x y →
      subst (λ a → T C (map f a)) (q x) (transport f (transport g y))
      ≡ transport f (subst (T B) (q x) (transport g y))
    transport-nat x y = subst
      (λ b → ∀ (eq : map g x ≡ b) →
        subst (λ a → T C (map f a)) eq (transport f (transport g y))
        ≡ transport f (subst (T B) eq (transport g y)))
      (q x)
      (λ { refl → refl })
      (q x)

    r̂ : ∀ {x : U A} (y : T A x)
                → ≡.subst (T C) (r x) (transport f (transport g y))
                ≡ transport h (transport i y)
    r̂ {x} y =
      subst (T C) (r x) (transport f (transport g y))
        ≡⟨ sym (subst² (T C) (cong (map f) (q x)) (p (map i x))
                  (transport f (transport g y))) ⟩
      subst (T C) (p (map i x)) (subst (T C) (cong (map f) (q x))
        (transport f (transport g y)))
        ≡⟨ cong (subst (T C) (p (map i x)))
                (subst-cong (map f) (T C) (q x) (transport f (transport g y))) ⟩
      subst (T C) (p (map i x)) (subst (λ a → T C (map f a)) (q x)
        (transport f (transport g y)))
        ≡⟨ cong (subst (T C) (p (map i x))) (transport-nat x y) ⟩
      subst (T C) (p (map i x)) (transport f (subst (T B) (q x) (transport g y)))
        ≡⟨ cong (λ z → subst (T C) (p (map i x)) (transport f z)) (q̂ y) ⟩
      subst (T C) (p (map i x)) (transport f (transport i y))
        ≡⟨ p̂ (transport i y) ⟩
      transport h (transport i y) ∎

  -- The category of families of sets
  Cat : Category (lsuc (ℓU ⊔ ℓT)) (ℓU ⊔ ℓT) (ℓU ⊔ ℓT)
  Cat = record
    { Obj = Fam'
    ; _⇒_ = Hom
    ; _≈_ = λ f g → f ≡ꟳ g
    ; id = fam-id
    ; _∘_ = comp
    ; assoc = λ {A B C D f g h} → assoc {A} {B} {C} {D} {f} {g} {h}
    ; sym-assoc = λ {A B C D f g h} → feq (λ _ → refl) (λ _ → refl)
    ; identityˡ = λ {A B f} → identityˡ {A} {B} {f}
    ; identityʳ = λ {A B f} → identityʳ {A} {B} {f}
    ; identity² = λ {A} → identity² {A}
    ; equiv = record
      { refl = ≡ꟳ-refl
      ; sym = λ { p → ≡ꟳ-sym p }
      ; trans = λ {  p   q  →  ≡ꟳ-trans p q  }
      }
    ; ∘-resp-≈ = λ {  p   q  →  comp-resp-≡ꟳ p q  }
    }
    where
    open ≡.≡-Reasoning
    open ≡

    -- Associativity of composition
    assoc : {A B C D : Fam'} {f : Hom A B} {g : Hom B C} {h : Hom C D} →
      comp (comp h g) f ≡ꟳ comp h (comp g f)
    assoc {A} {B} {C} {D} {f} {g} {h} = feq (λ _ → refl) (λ _ → refl)

    -- Left identity
    identityˡ : {A B : Fam'} {f : Hom A B} → comp fam-id f ≡ꟳ f
    identityˡ {A} {B} {f} = feq (λ _ → refl) (λ _ → refl)

    -- Right identity
    identityʳ : {A B : Fam'} {f : Hom A B} → comp f fam-id ≡ꟳ f
    identityʳ {A} {B} {f} = feq (λ _ → refl) (λ _ → refl)

    -- Identity composition
    identity² : {A : Fam'} → comp fam-id fam-id ≡ꟳ fam-id {A}
    identity² {A} = feq (λ _ → refl) (λ _ → refl)

open FamCat public hiding (Cat)

-- Export the category constructor
FamilyOfSets : ∀ ℓU ℓT → Category (lsuc (ℓU ⊔ ℓT)) (ℓU ⊔ ℓT) (ℓU ⊔ ℓT)
FamilyOfSets ℓU ℓT = FamCat.Cat {ℓU} {ℓT}
