{-# OPTIONS --guarded #-}
module Scratch (A : Set) where

open import QIT.Prelude
open import QIT.Prop
open import Data.Bool
open import QIT.Container.Base
open import QIT.Functor.Base

record Stream : Set where
  coinductive
  field
    hd : A 
    tl : Stream

open Stream

record _~_ (xs ys : Stream) : Set where
  coinductive
  field
    eqhd : hd xs ≡ hd ys
    eqtl : tl xs ~ tl ys

module Mob1 where
  data M0 : Set where
    l0 : M0
    m0 : M0 → M0 → M0

  data ~0 : Set where
    p0 : ∀ (x y : M0) → ~0

  data M1 : M0 → Set where
    l1 : M1 l0
    m1 : (x0 y0 : M0) → M1 x0 → M1 y0 → M1 (m0 x0 y0)

  data _~1_∶_ : M0 → M0 → ~0 → Set where
    p1 : (x0 y0 : M0) → M1 x0 → M1 y0 → x0 ~1 y0 ∶ p0 x0 y0

module Mob2 where
  data S0 : Set where
    sl0 : S0 
    sm0 : S0 

  data P0 : S0 → Set where
    pl0 : ⊥ → P0 sl0
    pm0 : Bool → P0 sm0

  W0 : Set
  W0 = W S0 P0

  data S1 : W0 → Set where
    sl1 : S1 (sup (sl0 , λ {(pl0 ())}))  
    sm1 : (f : Bool → W0) → S1 (sup (sm0 , λ {(pm0 x) → f x}))
    -- m1 : (x0 y0 : M0) → M1 x0 → M1 y0 → M1 (m0 x0 y0)
    -- p1 : (x0 y0 : M0) → M1 x0 → M1 y0 → x0 ~1 y0 ∶ p0 x0 y0
