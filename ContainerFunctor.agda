{-# OPTIONS --type-in-type #-}
open import Prelude
open import Setoid
open import Equivalence
open import Data.Product

open import Data.Container hiding (refl; sym; trans)

module ContainerFunctor (C : Container lzero lzero) where

private
  l0 = lzero

module Ob (S : Setoid l0 l0) where
  open ≈.Setoid S
  record _≈ꟳ'_ (x y : ⟦ C ⟧ ⟨ S ⟩) : Set l0 where
    constructor mk≈ꟳ'
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst (C .Position) fst≡ p)

  _≈ꟳ_ = Trunc₂ _≈ꟳ'_
  pattern mk≈ꟳ fst≡ snd≈ = ∣ mk≈ꟳ' fst≡ snd≈ ∣

  isReflexive : Reflexive _≈ꟳ_
  isReflexive = mk≈ꟳ ≡.refl (λ p → refl)

  isSymmetric : Symmetric _≈ꟳ_
  isSymmetric {x} {y} (mk≈ꟳ fst≡ snd≈) =
    mk≈ꟳ (≡.sym fst≡) λ p → sym (snd≈⁻¹ p)
    where
    u : ∀ p → x .proj₂ (subst (C .Position) (≡.sym fst≡) p) ≈
              y .proj₂ (subst (C .Position) fst≡
                        (subst (C .Position) (≡.sym fst≡) p))
    u p = snd≈ (subst (C .Position) (≡.sym fst≡) p)
    v : ∀ p → (subst (C .Position) fst≡ (subst (C .Position) (≡.sym fst≡) p))
            ≡ p
    v p = ≡.subst-subst-sym fst≡
    snd≈⁻¹ : ∀ p → x .proj₂ (subst (C .Position) (≡.sym fst≡) p) ≈ y .proj₂ p
    snd≈⁻¹ p =
      substp (λ ○ → x .proj₂ (subst (C .Position) (≡.sym fst≡) p) ≈ y .proj₂ ○)
              (v p) (snd≈ (subst (C .Position) (≡.sym fst≡) p))

  isTransitive : Transitive _≈ꟳ_
  isTransitive {x = x} {y} {z} (mk≈ꟳ fst≡1 snd≈1) (mk≈ꟳ fst≡2 snd≈2) =
    mk≈ꟳ (≡.trans fst≡1 fst≡2) v
    where
    u : ∀ p → x .proj₂ p ≈ z .proj₂ (subst (C .Position) fst≡2 (subst (C .Position) fst≡1 p))
    u p = trans (snd≈1 p) (snd≈2 (subst (C .Position) fst≡1 p))
    v : ∀ p → x .proj₂ p ≈ z .proj₂ (subst (C .Position) (≡.trans fst≡1 fst≡2) p)
    v p = substp (λ ○ → x .proj₂ p ≈ z .proj₂ ○) (≡.subst-subst fst≡1) (u p)

  F̃-ob : Setoid l0 l0
  F̃-ob = record
    { Carrier = ⟦ C ⟧ ⟨ S ⟩
    ; _≈_ = _≈ꟳ_
    ; isEquivalence = record
      { refl = isReflexive
      ; sym = isSymmetric
      ; trans = isTransitive } }

open Ob using (F̃-ob)

module Mor {S T : Setoid l0 l0} (f : ≈.Hom S T) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module f = ≈.Hom f
  ⟦_⟧h : ⟦ C ⟧ ⟨ S ⟩ → ⟦ C ⟧ ⟨ T ⟩
  ⟦ s , g ⟧h = s , λ x → f.⟦ g x ⟧
  congh : ∀ {x y} → (F̃-ob S Setoid.≈ x) y → (T Ob.≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
  congh (Ob.mk≈ꟳ fst≡ snd≈) = Ob.mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))
  F̃-mor : ≈.Hom (F̃-ob S) (F̃-ob T)
  F̃-mor = record
    { ⟦_⟧ = ⟦_⟧h
    ; cong = congh
    }

open Mor using (F̃-mor)

module Comp {S T U : Setoid l0 l0} (f : ≈.Hom S T) (g : ≈.Hom T U) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module U = ≈.Setoid U
  module f = ≈.Hom f
  module g = ≈.Hom g

  F̃-comp : ≈.Hom≈ (F̃-mor (g ≈.∘ f)) (F̃-mor g ≈.∘ F̃-mor f)
  F̃-comp (Ob.mk≈ꟳ fst≡ snd≈) =
    Ob.mk≈ꟳ fst≡ λ p → (≈.Hom.cong g) ((≈.Hom.cong f) (snd≈ p))

open Comp using (F̃-comp)

module Resp
  {S T : Setoid l0 l0}
  {f g : ≈.Hom S T}
  (f≈g : f ≈h g)
  where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module f = ≈.Hom f
  module g = ≈.Hom g

  open Mor {S} {T} hiding (F̃-mor)

  F̃-resp : F̃-mor f ≈h F̃-mor g
  F̃-resp (Ob.mk≈ꟳ fst≡ snd≈) =
    Ob.mk≈ꟳ fst≡ λ p → f≈g (snd≈ p)

open Resp using (F̃-resp)

F̃ : ≈.Functor l0 l0
F̃ = record
  { F-ob = F̃-ob
  ; F-mor = F̃-mor
  ; F-id = λ p → p
  ; F-comp = F̃-comp
  ; F-resp = F̃-resp }
