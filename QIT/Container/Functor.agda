open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Binary
open import Data.Product

open import QIT.Container.Base

module QIT.Container.Functor {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓA ℓA' : Level) where

module Ob (A : Setoid ℓA ℓA') where
  open ≈.Setoid A
  record _≈ꟳ'_ (x y : ⟦ S ◁ P ⟧ ⟨ A ⟩) : Set (ℓS ⊔ ℓP ⊔ ℓA') where
    constructor mk≈ꟳ'
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst P fst≡ p)

  _≈ꟳ_ = Trunc₂ _≈ꟳ'_
  pattern mk≈ꟳ fst≡ snd≈ = ∣ mk≈ꟳ' fst≡ snd≈ ∣

  flatten≈ꟳ : ∀ s f g → (s , f) ≈ꟳ (s , g) → ∀ p → f p ≈ g p
  flatten≈ꟳ s f g (mk≈ꟳ ≡.refl snd≈) = snd≈

  isReflexive : Reflexive _≈ꟳ_
  isReflexive = mk≈ꟳ ≡.refl (λ p → refl)

  isSymmetric : Symmetric _≈ꟳ_
  isSymmetric {x} {y} (mk≈ꟳ fst≡ snd≈) =
    mk≈ꟳ (≡.sym fst≡) λ p → sym (snd≈⁻¹ p)
    where
    u : ∀ p → x .proj₂ (subst P (≡.sym fst≡) p) ≈
              y .proj₂ (subst P fst≡
                        (subst P (≡.sym fst≡) p))
    u p = snd≈ (subst P (≡.sym fst≡) p)
    v : ∀ p → (subst P fst≡ (subst P (≡.sym fst≡) p))
            ≡ p
    v p = ≡.subst-subst-sym fst≡
    snd≈⁻¹ : ∀ p → x .proj₂ (subst P (≡.sym fst≡) p) ≈ y .proj₂ p
    snd≈⁻¹ p =
      substp (λ ○ → x .proj₂ (subst P (≡.sym fst≡) p) ≈ y .proj₂ ○)
              (v p) (snd≈ (subst P (≡.sym fst≡) p))

  isTransitive : Transitive _≈ꟳ_
  isTransitive {x = x} {y} {z} (mk≈ꟳ fst≡1 snd≈1) (mk≈ꟳ fst≡2 snd≈2) =
    mk≈ꟳ (≡.trans fst≡1 fst≡2) v
    where
    u : ∀ p → x .proj₂ p ≈ z .proj₂ (subst P fst≡2 (subst P fst≡1 p))
    u p = trans (snd≈1 p) (snd≈2 (subst P fst≡1 p))
    v : ∀ p → x .proj₂ p ≈ z .proj₂ (subst P (≡.trans fst≡1 fst≡2) p)
    v p = substp (λ ○ → x .proj₂ p ≈ z .proj₂ ○) (≡.subst-subst fst≡1) (u p)

  F-ob : Setoid (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
  F-ob = record
    { Carrier = ⟦ S ◁ P ⟧ ⟨ A ⟩
    ; _≈_ = _≈ꟳ_
    ; isEquivalence = record
      { refl = isReflexive
      ; sym = isSymmetric
      ; trans = isTransitive } }

open Ob using (F-ob) public

module Mor {A B : Setoid ℓA ℓA'} (f : ≈.Hom A B) where
  module A = ≈.Setoid A
  module B = ≈.Setoid B
  module f = ≈.Hom f
  ⟦_⟧h : ⟦ S ◁ P ⟧ ⟨ A ⟩ → ⟦ S ◁ P ⟧ ⟨ B ⟩
  ⟦ s , g ⟧h = s , λ x → f.to (g x)
  congh : ∀ {x y} → (F-ob A Setoid.≈ x) y → (B Ob.≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
  congh (Ob.mk≈ꟳ fst≡ snd≈) = Ob.mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))
  F-mor : ≈.Hom (F-ob A) (F-ob B)
  F-mor = record
    { to = ⟦_⟧h
    ; cong = congh
    }

open Mor using (F-mor) public

module Comp {S T U : Setoid ℓA ℓA'} (f : ≈.Hom S T) (g : ≈.Hom T U) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module U = ≈.Setoid U
  module f = ≈.Hom f
  module g = ≈.Hom g

  F-comp : F-mor (g ≈.∘ f) ≈h (F-mor g ≈.∘ F-mor f)
  F-comp (Ob.mk≈ꟳ fst≡ snd≈) =
    Ob.mk≈ꟳ fst≡ λ p → (≈.Hom.cong g) ((≈.Hom.cong f) (snd≈ p))

open Comp using (F-comp) public

module Resp
  {S T : Setoid ℓA ℓA'}
  (f g : ≈.Hom S T)
  (f≈g : f ≈h g)
  where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module f = ≈.Hom f
  module g = ≈.Hom g

  open Mor {S} {T} hiding (F-mor)

  F-resp : F-mor f ≈h F-mor g
  F-resp (Ob.mk≈ꟳ fst≡ snd≈) =
    Ob.mk≈ꟳ fst≡ λ p → f≈g (snd≈ p)

open Resp using (F-resp) public

F : ≈.Functor ℓA ℓA' (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
F = record
  { F-ob = F-ob
  ; F-mor = F-mor
  ; F-id = λ p → p
  ; F-comp = F-comp
  ; F-resp = F-resp }
