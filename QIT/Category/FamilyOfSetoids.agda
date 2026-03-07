{-# OPTIONS --type-in-type #-}
module QIT.Category.FamilyOfSetoids where
-- Based off https://github.com/agda/agda-categories/blob/14e7fa985f115c77f154a04ecfd4973560293505/src/Categories/Category/Instance/FamilyOfSetoids.agda

open import QIT.Prelude
open import QIT.Setoid
open import QIT.Category.Base hiding (_[_≈_])
open import QIT.Relation.Binary using (IsEquivalence)

module _ {ℓU ℓU' ℓT ℓT' : Level} where
  open ≈.Hom
  record Fam : Set (lsuc (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')) where
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

  record Hom (B B' : Fam) : Set (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') where
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

  fam-id : {A : Fam} → Hom A A
  fam-id {A} = fhom ≈.idHom (λ _ → ≈.idHom)
    λ {x} p {bx} → Setoid.refl (T A x)

  comp : {A B C : Fam} → Hom B C → Hom A B → Hom A C
  comp {B = B} {C = C} (fhom gmap gtrans gcoh) (fhom fmap ftrans fcoh) =
    fhom (gmap ≈.∘ fmap)
         (λ x → gtrans (fmap .to x) ≈.∘ ftrans x)
         λ {x} {y} p {bx} →
           let open Setoid (T C (gmap .to (fmap .to x))) renaming (trans to _⟨≈⟩_) in
           gtrans (fmap .to x) .cong (fcoh p {bx}) ⟨≈⟩
           gcoh (fmap .cong p) {ftrans y .to bx}

  ≈≈-refl : ∀ {A B} → {f : Hom A B} → f ≋ f
  ≈≈-refl {A} {B} {f} = feq (≈.≈h-refl {f = f.map})
    λ {x} {bx} → reindex-refl B {f.to x} {f .Hom.transport x .to bx}
    where module f = Hom f

  ≈≈-sym : ∀ {A B} → {f g : Hom A B} → f ≋ g → g ≋ f
  ≈≈-sym {A} {B} {f} {g} (feq ≈map ≈fibre) =
    feq (≈.≈h-sym {f = f.map} {g = g.map} ≈map)
    λ {x} {bx} →
      let open ≈.≈syntax {S = T B (g.to x)} in
      let open Setoid (T B (g.to x)) in
      let p = ≈map {x} in
        (reindex B _ ≈.∘ f.transport x) .to bx
          ≈⟨ sym (B.reindex (Setoid.sym (U B) p) .cong ≈fibre) ⟩
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

  ≈≈-trans : ∀ {A B} → {f g h : Hom A B} → f ≋ g → g ≋ h → f ≋ h
  ≈≈-trans {A} {B} {f} {g} {h} (feq ≈map1 ≈fibre1) (feq ≈map2 ≈fibre2) =
    feq (≈.≈h-trans {S = A.U} {T = B.U} ≈map1 ≈map2)
    λ {x} {bx} →
      let trans = Setoid.trans (T B (Hom.map f .to x)) in
      let sym = Setoid.sym (T B (Hom.map f .to x)) in

      let step1 = reindex-trans B (≈map2 {x}) (≈map1 {x}) (Hom.transport h x .to bx) in
      -- reindex p1 (reindex p2 (h.trans)) ≈ reindex (trans p1 p2) (h.trans)

      let step2 = reindex B (≈map1 {x}) .cong (≈fibre2 {x} {bx}) in
      -- reindex p1 (reindex p2 (h.trans)) ≈ reindex p1 (g.trans)

      let step3 = ≈fibre1 {x} {bx} in
      -- reindex p1 (g.trans) ≈ f.trans

      trans (sym step1) (trans step2 step3)
    where
    module f = Hom f
    module g = Hom g
    module A = Fam A
    module B = Fam B

  comp-resp-≈ : {A B C : Fam} {f h : Hom B C} {g i : Hom A B} →
      f ≋ h → g ≋ i → comp f g ≋ comp h i
  comp-resp-≈ {A} {B} {C} {f} {h} {g} {i} (feq f≈h t-f≈h) (feq g≈i t-g≈i) =
    feq (≈.∘-resp-≈ f≈h g≈i)
        λ {x} {bx} →
          let u = Hom.map g .to x in
          let v = Hom.map i .to x in
          let p_g = g≈i {x} in -- p_g : g x ≈ i x
          let p_f = Hom.map f .cong p_g in -- p_f : f (g x) ≈ f (i x)
          let p_fh = f≈h {v} in -- p_fh : f (i x) ≈ h (i x)

          let trans = Setoid.trans (T C (Hom.map f .to u)) in
          let sym = Setoid.sym (T C (Hom.map f .to u)) in

          -- 1. reindex (trans p_fh p_f) (...) ≈ reindex p_f (reindex p_fh (...))
          let step1 = reindex-trans C p_fh p_f (Hom.transport h v .to (Hom.transport i x .to bx)) in

          -- 2. reindex p_f (reindex p_fh (h.trans (i x) (...))) ≈ reindex p_f (f.trans (i x) (...))
          let step2 = reindex C p_f .cong (t-f≈h {v} {Hom.transport i x .to bx}) in

          -- 3. reindex p_f (f.trans (i x) (...)) ≈ f.trans (g x) (reindex p_g (...))
          let step3 = Hom.transport-coh f p_g {Hom.transport i x .to bx} in

          -- 4. f.trans (g x) (reindex p_g (i.trans x bx)) ≈ f.trans (g x) (g.trans x bx)
          let step4 = Hom.transport f u .cong (t-g≈i {x} {bx}) in

          trans (sym step1) (trans step2 (trans (sym step3) step4))

  Cat : Category (lsuc (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')) (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')
  Cat = record
    { Obj = Fam
    ; _⇒_ = Hom
    ; _≈_ = _≋_
    ; id = fam-id
    ; _∘_ = comp
    ; assoc     = λ {A B C D f g h} → feq ≈.≈h-refl (refl-assoc {A} {B} {C} {D} {f} {g} {h})
    ; sym-assoc = λ {A B C D f g h} → feq ≈.≈h-refl (refl-assoc {A} {B} {C} {D} {f} {g} {h})
    ; identityˡ = λ {A B f} → feq ≈.≈h-refl (λ {x} {bx} → reindex-refl B {Hom.map f .to x} {Hom.transport f x .to bx})
    ; identityʳ = λ {A B f} → feq ≈.≈h-refl (λ {x} {bx} → reindex-refl B {Hom.map f .to x} {Hom.transport f x .to bx})
    ; identity² = λ {A} → feq ≈.≈h-refl (λ {x} {bx} → reindex-refl A {x} {bx})
    ; equiv = record
      { refl = ≈≈-refl
      ; sym = ≈≈-sym
      ; trans = ≈≈-trans
      }
    ; ∘-resp-≈ = comp-resp-≈
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
      refl-assoc {A} {B} {C} {D} {f} {g} {h} {x} {bx} =
        reindex-refl D {Hom.map h .to (Hom.map g .to (Hom.map f .to x))}
                       {Hom.transport h _ .to (Hom.transport g _ .to (Hom.transport f x .to bx))}

FamilyOfSetoids : ∀ ℓU ℓU' ℓT ℓT' → Category (lsuc (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')) (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT') (ℓU ⊔ ℓU' ⊔ ℓT ⊔ ℓT')
FamilyOfSetoids ℓU ℓU' ℓT ℓT' = Cat {ℓU} {ℓU'} {ℓT} {ℓT'}
