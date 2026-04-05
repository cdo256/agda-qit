{-# OPTIONS --type-in-type #-}
module QIT.Topology.Properties where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Topology.Subset
open import QIT.Topology.PointSet as PointSet
open import QIT.Topology.Filtered as Filtered

private
  variable
    ℓ𝓤 ℓ𝓟 ℓ𝓞 : Level

FilteredSpace→Space : ∀ {ℓ𝓤 ℓ𝓟 ℓ𝓞} → Filtered.Space ℓ𝓤 ℓ𝓟 ℓ𝓞 → PointSet.Space _ _ _
FilteredSpace→Space {ℓ𝓤} {ℓ𝓟} {ℓ𝓞} S = record
  { 𝓤 = 𝓤
  ; 𝓞 = 𝓞
  ; ∅∈𝓞 = ∅∈𝓞
  ; 𝓤∈𝓞 = 𝓤∈𝓞
  ; ⋃∈𝓞 = ⋃∈𝓞
  ; ∩∈𝓞 = ∩∈𝓞 }
  where
  open Filtered.Space S
    
Space→FilteredSpace : ∀ {ℓ𝓤 ℓ𝓟 ℓ𝓞} → PointSet.Space ℓ𝓤 ℓ𝓟 ℓ𝓞 → Filtered.Space _ _ _
Space→FilteredSpace {ℓ𝓤} {ℓ𝓟} {ℓ𝓞} S = record
  { 𝓤 = 𝓤
  ; 𝓝 = 𝓝
  ; isFilter = λ x → record
    { 𝓤∈ℱ = 𝓤∈𝓝 x
    ; ∅∉ℱ = λ Nx → absurdp (pt∈𝓝 _ ∅ Nx)
    ; ⊂∈ℱ = ⊂∈𝓝 x
    ; ∩∈ℱ = ∩∈𝓝 x }
  ; pt∈𝓝 = pt∈𝓝
  ; core = {!!} }
  where
  open PointSet.Space S
  data 𝓝 : 𝓤 → 𝓟 _ 𝓤 → Prop _ where
    𝓤∈𝓝 : ∀ x → 𝓝 x 𝓤̇
    ⊂∈𝓝 : ∀ x → (X Y : 𝓟 ℓ𝓟 𝓤) → 𝓝 x X → X ⊂ Y → 𝓝 x Y
    ∩∈𝓝 : ∀ x → (X Y : 𝓟 ℓ𝓟 𝓤) → 𝓝 x X → 𝓝 x Y → 𝓝 x (X ∩ Y)
  pt∈𝓝 : ∀ x N → 𝓝 x N → x ∈ N
  pt∈𝓝 x N (𝓤∈𝓝 x) = tt*
  pt∈𝓝 x N (⊂∈𝓝 x M N Mx M⊂N) = M⊂N x (pt∈𝓝 x M Mx)
  pt∈𝓝 x N (∩∈𝓝 x M M' Mx M'x) = pt∈𝓝 x M Mx , pt∈𝓝 x M' M'x
  core : ∀ x N → 𝓝 x N
       → ΣP (𝓟 _ 𝓤) (λ M → 𝓝 x M ∧ ((y : 𝓤) → y ∈ M → 𝓝 y N))
  -- core x N Nx = ⋃ (ΣP 𝓤 (_∈ N)) (λ (y , y∈N) z → {!!}) , {!!}
  -- core is neighborhood such that every element y ∈ M has N as its neighborhood.
  core x N Nx = {!!} , {!!} , λ y y∈M → {!!}
  

