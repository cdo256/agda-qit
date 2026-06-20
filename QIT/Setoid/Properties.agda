open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Base
open import QIT.Relation.Binary
open import QIT.Setoid.Base
import QIT.Setoid.Indexed as Ix

module QIT.Setoid.Properties where

module _ {ℓS ℓS'} (S : Setoid ℓS ℓS') where
  private
    A = ⟨ S ⟩

  cast : {w x y z : A} → w ≡ x → y ≡ z
       → S [ w ≈ y ] → S [ x ≈ z ]
  cast ≡.refl ≡.refl r = r

  castʳ : {x y z : A} → y ≡ z
        → S [ x ≈ y ] → S [ x ≈ z ]
  castʳ ≡.refl p = p

  castˡ : {x y z : A} → x ≡ y
        → S [ x ≈ z ] → S [ y ≈ z ]
  castˡ ≡.refl p = p

module _ {ℓI ℓS ℓS'} (S : Ix.Setoid ℓI ℓS ℓS') where
    open Ix.Setoid S

    transport≈ : ∀ {a b} (p : a ≡ b) {x y : A a}
      → S Ix.[ x ≈ y ] → S Ix.[ subst A p x ≈ subst A p y ]
    transport≈ ≡.refl p = p
