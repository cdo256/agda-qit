{-# OPTIONS --type-in-type #-}
module QIT.Mobile.Cocontinuity (B : Set) (inhabB : B) where

open import QIT.Prelude
open import QIT.Relation.Binary
open import QIT.Mobile.Base B
open import QIT.Mobile.Diagram B inhabB
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Unit
open import Data.Sum
open import QIT.Relation.Plump Branch

private
  l0 : Level
  l0 = lzero

open import QIT.Diagram ≤p
open import QIT.Colimit ≤p
open import QIT.ContainerFunctor Branch
open import QIT.Cocontinuity ≤p

module F = ≈.Functor F̃
module D = Diagram D

ϕ₀ : ⟨ Colim (F̃ ∘ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (i , (l , _)) = l , (λ ())
ϕ₀ (i , (n , f)) = n , (λ b → i , f b)

𝟘 : BTree
𝟘 = sup (l , λ())
suc : BTree → BTree
suc x = sup (n , λ _ → x)

ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F̃ ∘ D) ⟩
ψ₀ (l , _) = suc 𝟘 , (l , λ ())
ψ₀ (n , f) = sup (n , g) , (n , h)
  where
  g : B → W Branch
  g b = f b .proj₁
  h : B → ⟨ Diagram.D-ob D (sup (n , g)) ⟩
  h b = node g λ c → f c .proj₂

linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
linv (l , f) = begin
  ϕ₀ (ψ₀ (l , f))
    ≈⟨ refl ⟩
  (l , λ ())
    ≈⟨ {!!} ⟩
  (l , f) ∎
  where
    open ≈.≈syntax {S = (F.F-ob (Colim D))}
    open Setoid (F.F-ob (Colim D))
linv (n , f) = {!!}

cocontinuous : Cocontinuous F̃ D
cocontinuous = ∣ iso ∣
  where
  iso : ≈.Iso (Colim (F̃ ∘ D)) (F.F-ob (Colim D))
  iso = record
    { ⟦_⟧ = ϕ₀
    ; ⟦_⟧⁻¹ = ψ₀
    ; cong = {!!}
    ; cong⁻¹ = {!!}
    ; linv = linv
    ; rinv = {!!}
    }

