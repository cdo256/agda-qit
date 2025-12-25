{-# OPTIONS --type-in-type #-}
module Mobile.Colimit (B : Set) where

open import Prelude
open import Equivalence
open import Mobile.Base B
open import Mobile.Equivalence B
open import Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)
open import Data.Unit
open import Data.Sum
open import Plump Branch
open import Colimit ≤p
open import Subset
open import Order

private
  l0 : Level
  l0 = lzero




record Sz₀ (t : BTree) : Set l0 where
  constructor sz
  field
    u : BTree
    u<t : u < t

-- Sz : BTree → Setoid l0 l0
-- Sz t = record
--   { Carrier = Sz₀ t
--   ; _≈_ = λ (sz u _) (sz s _) → u ≈ᵗ s
--   ; isEquivalence = record
--     { refl = ≈refl
--     ; sym = ≈sym
--     ; trans = ≈trans } }

-- P : ∀ {t u} → u ≤ t → ≈.Hom (Sz u) (Sz t)
-- P {t} {u} u≤t = record
--   { ⟦_⟧ = λ (sz s s<u) → sz s (≤< u≤t s<u)
--   ; cong = λ s≈u → s≈u }

-- module ≤ = IsPreorder isPreorder-≤

-- Id : ∀ {t : BTree}
--     → ≈.Hom≈ (P (≤refl t)) ≈.idHom 
-- Id p = p

-- Comp : ∀{s t u} (p : s ≤ t) (q : t ≤ u)
--       → ≈.Hom≈ (P (≤.trans p q)) (P q ≈.∘ P p)   
-- Comp _ _ r = r

-- D : Diagram
-- D = record
--   { D-ob = Sz
--   ; D-mor = P
--   ; D-id = λ {i} {x} {y} → Id {i} {x} {y}
--   ; D-comp = Comp }

-- open Colim D
