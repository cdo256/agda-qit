{-# OPTIONS --type-in-type #-}
open import Prelude
open import Data.Product
open import Data.W
open import Data.Container
open import Setoid.Base

module Plump {ℓs ℓp} (C : Container ℓs ℓp) where

-- From Fiore et al. 2022
Size : Set (ℓs ⊔ ℓp) 
Size = W C
-- The well-founded order (<) on Size
mutual
  infix 4 _≤_ _<_
  data _≤_ : Size → Size → Prop (ℓs ⊔ ℓp) where
    sup≤ :
      {a   : Shape C}
      {f   : Position C a → Size}
      {i   : Size}
      (f<i : ∀ x → f x < i)
      → ---------------------
      sup (a , f) ≤ i
  data _<_ : Size → Size → Prop (ℓs ⊔ ℓp) where
    <sup :
      {a    : Shape C}
      {f    : Position C a → Size}
      (x    : Position C a)
      {i    : Size}
      (i≤fx : i ≤ f x)
      → ----------------------
      i < sup (a , f)
≤refl : ∀ i → i ≤ i
≤refl (sup (_ , f)) = sup≤ (λ x → <sup x (≤refl (f x)))

mutual
  ≤≤ : {i j k : Size} → j ≤ k → i ≤ j → i ≤ k
  ≤≤ j≤k (sup≤ f<i) = sup≤ λ x → ≤< j≤k (f<i x)

  ≤< : {i j k : Size} → j ≤ k → i < j → i < k
  ≤< (sup≤ f<i) (<sup x i≤fx) = <≤ (f<i x) i≤fx

  <≤ : {i j k : Size} → j < k → i ≤ j → i < k
  <≤ (<sup x i≤fx) i≤j = <sup x (≤≤ i≤fx i≤j)

<→≤ : ∀{i j} → i < j → i ≤ j
<→≤ (<sup x (sup≤ f<i)) = sup≤ (λ y → <sup x (<→≤ (f<i y)))

<< : ∀{i j k} → j < k → i < j → i < k
<< (<sup x i≤fx) i<j = <sup x (<→≤ (≤< i≤fx i<j))

open import Order

iswf< : WellFounded _<_
iswf< i = acc λ j j<i → α i j (<→≤ j<i)
  where
  α : ∀ i j → j ≤ i → Acc _<_ j
  α (sup (_ , f)) j j≤i = acc α'
    where
    α' : WfRec _<_ (Acc _<_) j
    α' k k<j with ≤< j≤i k<j
    ... | <sup x k≤fx = α (f x) k k≤fx

isPreorder-≤ : IsPreorder _≤_
isPreorder-≤ = record
  { refl = λ {x} → ≤refl x
  ; trans = λ p q → ≤≤ q p }

≤p : Preorder (W C) _
≤p = _≤_ , isPreorder-≤
