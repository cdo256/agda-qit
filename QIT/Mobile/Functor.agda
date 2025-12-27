{-# OPTIONS --type-in-type #-}
module QIT.Mobile.Functor (B : Set) where

open import QIT.Prelude
open import QIT.Mobile.Base B
open import QIT.Relation.Binary
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)

private
  l0 : Level
  l0 = lzero

module Ob (S : Setoid l0 l0) where
  private
    module S = Setoid S
  F̃-ob₀ : Set
  F̃-ob₀ = ⟦ Branch ⟧ ⟨ S ⟩
  data _≈ᵗ_ : F̃-ob₀ → F̃-ob₀ → Prop l0 where
    ≈leaf : ∀ {f g} → (l , f) ≈ᵗ (l , g)
    ≈node : ∀ {f g} → (c : ∀ b → f b S.≈ g b)
          → (n , f) ≈ᵗ (n , g)
    ≈perm : ∀ {f} → (π : B ↔ B)
          → (n , f) ≈ᵗ (n , λ b → f (π .↔.to b))
    ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

  ≈refl : ∀ {t} → t ≈ᵗ t
  ≈refl {(l , f)} = ≈leaf
  ≈refl {(n , f)} = ≈node λ b → S.refl

  ≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → S.sym (c b)
  ≈sym (≈perm {f} π) =
    substp A p q
    where
    module π = _↔_ π
    π' = ↔.flip π
    A : (B → B) → Prop l0
    A = λ h → (n , λ b → f (π.to b)) ≈ᵗ (n , λ b → f (h b))
    p : (λ b → π.to (π.from b)) ≡ (λ b → b)
    p = funExt λ b → π.linv b
    q : (n , λ b → f (π.to b)) ≈ᵗ (n , λ b → f (π.to (π.from b)))
    q = ≈perm {f = λ b → f (π.to b)} π'
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  isEquiv-≈ᵗ : IsEquivalence _≈ᵗ_
  isEquiv-≈ᵗ = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans }

  F̃-ob : Setoid l0 l0
  F̃-ob = record
    { Carrier = F̃-ob₀
    ; _≈_ = _≈ᵗ_
    ; isEquivalence = isEquiv-≈ᵗ }

  leaf≉node : ∀ {f g} → (l , g) ≈ᵗ (n , f) → ⊥p
  leaf≉node (≈trans {t = (l , _)} p q) = leaf≉node q
  leaf≉node (≈trans {t = (n , _)} p q) = leaf≉node p

  l≢n : l ≡ n → ⊥p
  l≢n ()

open Ob public

module Mor {S T : Setoid l0 l0} (f : ≈.Hom S T) where
  module f = ≈.Hom f

  ⟦_⟧h : ⟨ F̃-ob S ⟩ → ⟨ F̃-ob T ⟩
  ⟦ s , g ⟧h = s , λ b → f.to (g b)
  congh : ∀ {x y} → F̃-ob S [ x ≈ y ] → F̃-ob T [ ⟦ x ⟧h ≈ ⟦ y ⟧h ]
  congh {s , g} {t , h} ≈leaf = ≈leaf
  congh {s , g} {t , h} (≈node c) = ≈node (λ b → f.cong (c b))
  congh {s , g} {t , h} (≈perm π) = ≈perm π
  congh {s , g} {t , h} (≈trans p q) = ≈trans (congh p) (congh q)
  F̃-mor : ≈.Hom (F̃-ob S) (F̃-ob T)
  F̃-mor = record
    { to = ⟦_⟧h
    ; cong = congh
    }

open Mor using (F̃-mor)

module Comp {S T U : Setoid l0 l0} (f : ≈.Hom S T) (g : ≈.Hom T U) where
  module f = ≈.Hom f
  module g = ≈.Hom g

  F̃-comp : ≈.Hom≈ (F̃-mor (g ≈.∘ f)) (F̃-mor g ≈.∘ F̃-mor f)
  F̃-comp {s , h} {t , k} ≈leaf = ≈leaf
  F̃-comp {s , h} {t , k} (≈node c) = ≈node (λ b → (≈.Hom.cong g) ((≈.Hom.cong f) (c b)))
  F̃-comp {s , h} {t , k} (≈perm π) = ≈perm π
  F̃-comp {s , h} {t , k} (≈trans p q) = ≈trans (F̃-comp p) (F̃-comp q)

open Comp using (F̃-comp) public

module Resp
  {S T : Setoid l0 l0}
  {f g : ≈.Hom S T}
  (f≈g : f ≈h g)
  where
  module S = Setoid S
  module T = Setoid T
  -- module f = ≈.Hom f
  -- module g = ≈.Hom g

  open Mor {S} {T} hiding (F̃-mor)

  F̃-resp : F̃-mor f ≈h F̃-mor g
  F̃-resp {s , u} {t , v} (≈leaf) = ≈leaf
  F̃-resp {n , u} {n , v} (≈node c) = ≈node (λ b → f≈g (c b))
  F̃-resp {n , u} {n , v} (≈perm π) =
    ≈trans (≈perm π) (≈node (λ b → f≈g (S.refl)))
  F̃-resp {s , g} {u , h} (≈trans {t = t , i} p q) =
    ≈trans (F̃-resp p) {!F̃-resp ?!}

-- open Resp using (F̃-resp) public

-- F̃ : ≈.Functor l0 l0
-- F̃ = record
--   { F-ob = F̃-ob
--   ; F-mor = F̃-mor
--   ; F-id = λ p → p
--   ; F-comp = F̃-comp
--   ; F-resp = F̃-resp }
