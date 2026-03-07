{-# OPTIONS --type-in-type #-}
module QIT.Category.FamilyOfSetoids where
-- Based off https://github.com/agda/agda-categories/blob/14e7fa985f115c77f154a04ecfd4973560293505/src/Categories/Category/Instance/FamilyOfSetoids.agda

open import QIT.Prelude
open import QIT.Setoid
open import QIT.Category.Base hiding (_[_≈_])
open import QIT.Relation.Binary using (IsEquivalence)

record Fam (ℓU ℓU' ℓT ℓT' : Level) : Set (lsuc (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')) where
  constructor fam
  field
    U : Setoid ℓU ℓU'
  module U = Setoid U
  open ≈.Hom
  field
    T : ⟨ U ⟩ → Setoid ℓT ℓT'
    reindex : {x y : ⟨ U ⟩} (p : U [ x ≈ y ]) → ≈.Hom (T y) (T x)
    reindex-refl : {x : ⟨ U ⟩} {bx : ⟨ T x ⟩}
      → T x [ reindex U.refl .to bx ≈ bx ]
    reindex-sym-sect : {x y : ⟨ U ⟩} (p : x U.≈ y) (bx : ⟨ T x ⟩)
      → T x [ reindex p .to (reindex (U.sym p) .to bx) ≈ bx ]
    reindex-sym-retr : {x y : ⟨ U ⟩} (p : x U.≈ y) (by : ⟨ T y ⟩)
      → T y [ reindex (U.sym p) .to (reindex p .to by) ≈ by ]
    reindex-trans : {x y z : ⟨ U ⟩} (p : y U.≈ x) (q : z U.≈ y) (bx : ⟨ T x ⟩)
      → T z [ reindex q .to (reindex p .to bx) ≈ reindex (U.trans q p) .to bx ]
open Fam

module FamCat {ℓU ℓU' ℓT ℓT' : Level} where
  private
    Fam' = Fam ℓU ℓU' ℓT ℓT'
  open ≈.Hom
  record Hom (B B' : Fam') : Set (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') where
    constructor fhom
    open Setoid (U B) using (_≈_)
    field
      map : ≈.Hom (U B) (U B')
      transport : (x : Setoid.Carrier (U B)) → ≈.Hom (T B x) (T B' (map .to x))
      transport-coh : {x y : Setoid.Carrier (U B)} → (p : x ≈ y)
        → (T B y ≈.⇨ T B' (map .to x))
        [ (transport x ≈.∘ reindex B p)
        ≈ (reindex B' (map .cong p) ≈.∘ transport y) ]
    open ≈.Hom map public

  record _≋_ {A B} (f g : Hom A B) : Prop (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') where
    constructor feq
    module f = Hom f
    module g = Hom g
    field
      ≈map : f.map ≈h g.map
      ≈fibre : ∀ {x : ⟨ A .U ⟩}
        → let C = T A x ; D = T B (f.to x)
          in (reindex B (≈map {x}) ≈.∘ g.transport x)
          ≈h (f.transport x)

  fam-id : {A : Fam'} → Hom A A
  fam-id {A} = fhom ≈.idHom (λ _ → ≈.idHom)
    λ {x} p {bx} → Setoid.refl (T A x)

  comp : {A B C : Fam'} → Hom B C → Hom A B → Hom A C
  comp {B = B} {C = C} (fhom gmap gtrans gcoh) (fhom fmap ftrans fcoh) =
    fhom (gmap ≈.∘ fmap)
         (λ x → gtrans (fmap .to x) ≈.∘ ftrans x)
         λ {x} {y} p {bx} →
           let open Setoid (T C (gmap .to (fmap .to x))) renaming (trans to _⟨≈⟩_) in
           gtrans (fmap .to x) .cong (fcoh p {bx}) ⟨≈⟩
           gcoh (fmap .cong p) {ftrans y .to bx}

  ≋-refl : ∀ {A B} → {f : Hom A B} → f ≋ f
  ≋-refl {A} {B} {f} = feq (≈.≈h-refl {f = f.map})
    λ {x} {bx} → reindex-refl B {f.to x} {f .Hom.transport x .to bx}
    where module f = Hom f

  ≋-sym : ∀ {A B} → {f g : Hom A B} → f ≋ g → g ≋ f
  ≋-sym {A} {B} {f} {g} (feq ≈map ≈fibre) =
    feq (≈.≈h-sym {f = f.map} {g = g.map} ≈map)
    λ {x} {bx} →
      let open ≈.≈syntax {S = T B (g.to x)} in
      let open Setoid (T B (g.to x)) in
      let p = ≈map {x} in
        (reindex B (Setoid.sym (U B) p) ≈.∘ f.transport x) .to bx
          ≈⟨ sym (B.reindex (Setoid.sym (U B) p) .cong (≈fibre {x} {bx})) ⟩
        B .reindex (Setoid.sym (U B) p) .to
          (B .reindex p .to
          (g.transport x .to bx))
          ≈⟨ reindex-sym-retr B p (g.transport x .to bx) ⟩
        g.transport x .to bx ∎
    where
    module f = Hom f
    module g = Hom g
    module A = Fam A
    module B = Fam B

  ≋-trans : ∀ {A B} → {f g h : Hom A B} → f ≋ g → g ≋ h → f ≋ h
  ≋-trans {A} {B} {f} {g} {h} (feq ≈map1 ≈fibre1) (feq ≈map2 ≈fibre2) =
    feq (≈.≈h-trans {S = Fam.U A} {T = Fam.U B} {f = f.map} {g = g.map} {h = h.map} ≈map1 ≈map2)
    λ {x} {bx} →
      let open ≈.≈syntax {S = T B (f.to x)} in
      let open Setoid (T B (f.to x)) in
      let p1 = ≈map1 {x} in
      let p2 = ≈map2 {x} in
        (reindex B (Setoid.trans (U B) p1 p2) ≈.∘ h.transport x) .to bx
          ≈⟨ sym (reindex-trans B p2 p1 (h.transport x .to bx)) ⟩
        reindex B p1 .to
          (reindex B p2 .to
          (h.transport x .to bx))
          ≈⟨ reindex B p1 .cong (≈fibre2 {x} {bx}) ⟩
        reindex B p1 .to (g.transport x .to bx)
          ≈⟨ ≈fibre1 {x} {bx} ⟩
        f.transport x .to bx ∎
    where
    module f = Hom f
    module g = Hom g
    module h = Hom h
    module A = Fam A
    module B = Fam B

  comp-resp-≋ : {A B C : Fam'} {f h : Hom B C} {g i : Hom A B} →
      f ≋ h → g ≋ i → comp f g ≋ comp h i
  comp-resp-≋ {A} {B} {C} {f} {h} {g} {i} (feq f≈h t-f≈h) (feq g≈i t-g≈i) =
    feq (≈.∘-resp-≈ {A = Fam.U A} {B = Fam.U B} {C = Fam.U C} {g₁ = f.map} {g₂ = h.map} {f₁ = g.map} {f₂ = i.map} f≈h g≈i)
        λ {x} {bx} →
          let u = g.to x in
          let v = i.to x in
          let p_g = g≈i {x} in
          let p_f = f.cong p_g in
          let p_fh = f≈h {v} in
          let open ≈.≈syntax {S = T C (f.to u)} in
          let open Setoid (T C (f.to u)) in
            (reindex C (Setoid.trans (U C) p_f p_fh) ≈.∘ (h.transport v ≈.∘ i.transport x)) .to bx
              ≈⟨ sym (reindex-trans C p_fh p_f (h.transport v .to (i.transport x .to bx))) ⟩
            reindex C p_f .to
              (reindex C p_fh .to
              (h.transport v .to
              (i.transport x .to bx)))
              ≈⟨ reindex C p_f .cong (t-f≈h {v} {i.transport x .to bx}) ⟩
            reindex C p_f .to (f.transport v .to (i.transport x .to bx))
              ≈⟨ sym (f.transport-coh p_g {i.transport x .to bx}) ⟩
            f.transport u .to (reindex B p_g .to (i.transport x .to bx))
              ≈⟨ f.transport u .cong (t-g≈i {x} {bx}) ⟩
            f.transport u .to (g.transport x .to bx) ∎
    where
    module f = Hom f
    module g = Hom g
    module h = Hom h
    module i = Hom i
    module A = Fam A
    module B = Fam B
    module C = Fam C

  Cat : Category (lsuc (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')) (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')
  Cat = record
    { Obj = Fam'
    ; _⇒_ = Hom
    ; _≈_ = _≋_
    ; id = fam-id
    ; _∘_ = comp
    ; assoc     = λ {A B C D f g h} → assoc {f = f} {g} {h}
    ; sym-assoc = λ {A B C D f g h} → ≋-sym (assoc {f = f} {g} {h})
    ; identityˡ = λ {A B f} → identityˡ {f = f}
    ; identityʳ = λ {A B f} → identityʳ {f = f}
    ; identity² = λ {A} → identity² {A}
    ; equiv = record
      { refl = ≋-refl
      ; sym = ≋-sym
      ; trans = ≋-trans
      }
    ; ∘-resp-≈ = comp-resp-≋
    }
    where
      refl-assoc : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D}
        → ∀ {x : ⟨ Fam.U A ⟩} {bx : ⟨ Fam.T A x ⟩}
        → Setoid._≈_ (Fam.T D (Hom.map h .to (Hom.map g .to (Hom.map f .to x))))
          (Fam.reindex D (Setoid.refl (Fam.U D)) .to
           (Hom.transport h (Hom.map g .to (Hom.map f .to x)) .to
            (Hom.transport g (Hom.map f .to x) .to
             (Hom.transport f x .to bx))))
          (Hom.transport h (Hom.map g .to (Hom.map f .to x)) .to
           (Hom.transport g (Hom.map f .to x) .to
            (Hom.transport f x .to bx)))
      refl-assoc {D = D} = reindex-refl D

      assoc : {A B C D : Fam'} {f : Hom A B} {g : Hom B C} {h : Hom C D} →
        comp (comp h g) f ≋ comp h (comp g f)
      assoc {A} {B} {C} {D} {f} {g} {h} = feq
        (≈.∘-assoc (Hom.map h) (Hom.map g) (Hom.map f))
        (λ {x} {bx} →
          reindex-refl D
            {x = Hom.map h .to (Hom.map g .to (Hom.map f .to x))}
            {bx = Hom.transport h _ .to (Hom.transport g _ .to (Hom.transport f x .to bx))})

      identityˡ : {A B : Fam'} {f : Hom A B} → comp fam-id f ≋ f
      identityˡ {B = B} {f} = feq
        (λ {x} → Setoid.refl (U B) {x = Hom.map f .to x})
        (λ {x} {bx} →
          reindex-refl B {x = Hom.map f .to x} {bx = Hom.transport f x .to bx})

      identityʳ : {A B : Fam'} {f : Hom A B} → comp f fam-id ≋ f
      identityʳ {B = B} {f} = feq
        (λ {x} → Setoid.refl (U B) {x = Hom.map f .to x})
        (λ {x} {bx} →
          reindex-refl B {x = Hom.map f .to x} {bx = Hom.transport f x .to bx})

      identity² : {A : Fam'} → comp fam-id fam-id ≋ fam-id
      identity² {A} = feq
        (λ {x} → Setoid.refl (U A) {x = x})
        (λ {x} {bx} → reindex-refl A {x = x} {bx = bx})

open FamCat public hiding (Cat)

FamilyOfSetoids : ∀ ℓU ℓU' ℓT ℓT' → Category (lsuc (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')) (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')
FamilyOfSetoids ℓU ℓU' ℓT ℓT' = FamCat.Cat {ℓU} {ℓU'} {ℓT} {ℓT'}
