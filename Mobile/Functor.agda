{-# OPTIONS --type-in-type #-}
module Mobile.Functor (B : Set) where

open import Prelude
open import Equivalence
open import Mobile.Base B
open import Mobile.Equivalence B
open import Mobile.Colimit B
open import Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)
open import Data.Unit
open import Data.Sum
open import Setoid
open import Equivalence
open import Data.Product
open import Data.Container hiding (refl; sym; trans)

private
  l0 : Level
  l0 = lzero

private
  Pos = Branch .Position


module Ob (S : Setoid l0 l0) where
  open ≈.Setoid S
  record _≈ꟳ'_ (x y : ⟦ Branch ⟧ ⟨ S ⟩) : Set l0 where
    constructor mk≈ꟳ'
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst Pos fst≡ p)

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
    u : ∀ p → x .proj₂ (subst Pos (≡.sym fst≡) p) ≈
              y .proj₂ (subst Pos fst≡
                        (subst Pos (≡.sym fst≡) p))
    u p = snd≈ (subst Pos (≡.sym fst≡) p)
    v : ∀ p → (subst Pos fst≡ (subst Pos (≡.sym fst≡) p))
            ≡ p
    v p = ≡.subst-subst-sym fst≡
    snd≈⁻¹ : ∀ p → x .proj₂ (subst Pos (≡.sym fst≡) p) ≈ y .proj₂ p
    snd≈⁻¹ p =
      substp (λ ○ → x .proj₂ (subst Pos (≡.sym fst≡) p) ≈ y .proj₂ ○)
              (v p) (snd≈ (subst Pos (≡.sym fst≡) p))

  isTransitive : Transitive _≈ꟳ_
  isTransitive {x = x} {y} {z} (mk≈ꟳ fst≡1 snd≈1) (mk≈ꟳ fst≡2 snd≈2) =
    mk≈ꟳ (≡.trans fst≡1 fst≡2) v
    where
    u : ∀ p → x .proj₂ p ≈ z .proj₂ (subst Pos fst≡2 (subst Pos fst≡1 p))
    u p = trans (snd≈1 p) (snd≈2 (subst Pos fst≡1 p))
    v : ∀ p → x .proj₂ p ≈ z .proj₂ (subst Pos (≡.trans fst≡1 fst≡2) p)
    v p = substp (λ ○ → x .proj₂ p ≈ z .proj₂ ○) (≡.subst-subst fst≡1) (u p)

  F̃-ob : Setoid l0 l0
  F̃-ob = record
    { Carrier = ⟦ Branch ⟧ ⟨ S ⟩
    ; _≈_ = _≈ꟳ_
    ; isEquivalence = record
      { refl = isReflexive
      ; sym = isSymmetric
      ; trans = isTransitive } }

open Ob using (F̃-ob; _≈ꟳ_; mk≈ꟳ; mk≈ꟳ') public

module Mor {S T : Setoid l0 l0} (f : ≈.Hom S T) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module f = ≈.Hom f
  ⟦_⟧h : ⟦ Branch ⟧ ⟨ S ⟩ → ⟦ Branch ⟧ ⟨ T ⟩
  ⟦ s , g ⟧h = s , λ x → f.⟦ g x ⟧
  congh : ∀ {x y} → (F̃-ob S Setoid.≈ x) y → (T Ob.≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
  congh (Ob.mk≈ꟳ fst≡ snd≈) = Ob.mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))
  F̃-mor : ≈.Hom (F̃-ob S) (F̃-ob T)
  F̃-mor = record
    { ⟦_⟧ = ⟦_⟧h
    ; cong = congh
    }

open Mor using (F̃-mor) public

module Comp {S T U : Setoid l0 l0} (f : ≈.Hom S T) (g : ≈.Hom T U) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module U = ≈.Setoid U
  module f = ≈.Hom f
  module g = ≈.Hom g

  F̃-comp : ≈.Hom≈ (F̃-mor (g ≈.∘ f)) (F̃-mor g ≈.∘ F̃-mor f)
  F̃-comp (Ob.mk≈ꟳ fst≡ snd≈) =
    Ob.mk≈ꟳ fst≡ λ p → (≈.Hom.cong g) ((≈.Hom.cong f) (snd≈ p))

open Comp using (F̃-comp) public  

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

open Resp using (F̃-resp) public

F̃ : ≈.Functor l0 l0
F̃ = record
  { F-ob = F̃-ob
  ; F-mor = F̃-mor
  ; F-id = λ p → p
  ; F-comp = F̃-comp
  ; F-resp = F̃-resp }
