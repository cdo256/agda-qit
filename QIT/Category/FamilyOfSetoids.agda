{-# OPTIONS --type-in-type #-}
module QIT.Category.FamilyOfSetoids where
-- Based off https://github.com/agda/agda-categories/blob/14e7fa985f115c77f154a04ecfd4973560293505/src/Categories/Category/Instance/FamilyOfSetoids.agda

open import QIT.Prelude
open import QIT.Setoid

module _ {ℓU ℓU' ℓT ℓT' : Level} where
  open ≈.Hom
  record Fam : Set _ where
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
  
  record Hom (B B' : Fam) : Set _ where
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

  record _≋_ {A B} (f g : Hom A B) : Set where
    constructor feq
    module f = Hom f
    module g = Hom g
    field
      ≈map : g.map ≈h f.map
      ≈fibre : ∀ {x : ⟨ A .U ⟩}
        → let C = T A x ; D = T B (f.to x)
          in (reindex B (B .U.sym (≈map {x})) ≈.∘ g.transport x)
          ≈h (f.transport x) 
      
