{-# OPTIONS --type-in-type #-}
module Mobile.Base (B : Set) where

open import Prelude
open import Equivalence
open import Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)

private
  l0 : Level
  l0 = lzero

data NodeType : Set where
  l : NodeType
  n : NodeType

open import Data.Unit
open import Data.Sum

Branch : Container l0 l0 
Branch .Shape = NodeType
Branch .Position l = ⊥*
Branch .Position n = B

BTree = W Branch

-- pattern leaf {f} = sup (l , f)
-- pattern node f = sup (n , f)

