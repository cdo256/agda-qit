{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.Mobile.Cocontinuity (B : Set) (inhabB :  ∥ B ∥) where

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

open import QIT.Diagram ≤p hiding (_≤_)
open import QIT.Colimit ≤p
open import QIT.Cocontinuity ≤p
open import QIT.Mobile.Functor B

module F = ≈.Functor F̃
module D = Diagram D

private
  L = Colim (F̃ ∘ D)
  R = F.F-ob (Colim D)

ϕ₀ : ⟨ Colim (F̃ ∘ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (i , (l , _)) = l , (λ ())
ϕ₀ (i , (n , f)) = n , (λ b → i , f b)

ϕ-cong : ∀ {x y} → Colim (F̃ ∘ D) [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
ϕ-cong (≈lstage i ≈leaf) = ≈leaf
ϕ-cong (≈lstage i (≈node c)) = ≈node λ b → ≈lstage i (c b)
ϕ-cong (≈lstage i (≈perm π)) = ≈perm π
ϕ-cong (≈lstage i {u , x} {v , x'} (≈trans {t = w , z} p q)) =
  ≈trans α β
  where
  α = ϕ-cong (≈lstage i p)
  β = ϕ-cong (≈lstage i q)
ϕ-cong (≈lstep {i} {j} p (l , _)) = ≈leaf
ϕ-cong (≈lstep {i} {j} (sup≤ p) (n , f)) = ≈node λ b → ≈lstep (sup≤ p) (f b)
ϕ-cong (≈lsym p) = ≈sym (Colim D) (ϕ-cong p)
ϕ-cong (≈ltrans p q) = ≈trans (ϕ-cong p) (ϕ-cong q)

ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F̃ ∘ D) ⟩
ψ₀ (l , _) = 𝟘 , (l , λ ())
ψ₀ (n , g) = t* , (n , h)
  where
  open Diagram D
  t : B → BTree
  t b = g b .proj₁
  f : ∀ b → P₀ (t b)
  f b = g b .proj₂
  t* : BTree
  t* = sup (n , t) 
  h : ∀ b → ⟨ D-ob t* ⟩
  h b = h'.to (f b)
    where 
    tb≤t* : t b ≤ t*
    tb≤t* = <→≤ (<sup b (≤refl (t b)))
    h' : ≈.Hom (D-ob (t b)) (D-ob t*)
    h' = D-mor tb≤t*
    module h' = ≈.Hom h'

ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ] → Colim (F̃ ∘ D) [ ψ₀ x ≈ ψ₀ y ]
ψ-cong ≈leaf = ≈lstage 𝟘 ≈leaf
ψ-cong (≈node {f} {g} c) = begin
  sup (n , f1) , (n , λ b → D-mor (fi≤sup n f1 b) .to (f2 b))
    ≈⟨ {!!} ⟩
  sup (n , f1) , (n , λ b → D-mor (fi≤sup n f1 b) .to (f2 b))
    ≈⟨ {!!} ⟩
  sup (n , g1) , (n , λ b → D-mor (fi≤sup n g1 b) .to (g2 b)) ∎
  where
  open Diagram D
  f1 : B → BTree
  f1 b = f b .proj₁
  f2 : ∀ b → P₀ (f1 b)
  f2 b = f b .proj₂
  g1 : B → BTree
  g1 b = f b .proj₁
  g2 : ∀ b → P₀ (g1 b)
  g2 b = f b .proj₂
  open ≈.Hom
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}
ψ-cong (≈perm π) = {!!}
ψ-cong (≈trans p q) = {!!}

linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
linv (l , f) = begin
  ϕ₀ (ψ₀ (l , f))
    ≈⟨ refl ⟩
  (l , λ ())
    ≈⟨ ≈leaf ⟩
  (l , f) ∎
  where
    open ≈.≈syntax {S = (F.F-ob (Colim D))}
    open Setoid (F.F-ob (Colim D))
linv (n , g) =
  ϕ₀ (ψ₀ (n , g))
    ≈⟨ refl ⟩
  (n , λ b → t* , weaken (t b) t* _ (f b))
    ≈⟨ ≈node (λ b → ≈lsym (≈lstep (fi≤sup n t b) (f b))) ⟩
  (n , λ b → t b , f b)
    ≈⟨ refl ⟩
  (n , g) ∎
  where
  open Setoid (F.F-ob (Colim D))
  open Diagram D
  t : B → BTree
  t b = g b .proj₁
  f : ∀ b → P₀ (t b)
  f b = g b .proj₂
  t* : BTree
  t* = sup (n , t) 
  --   open ≈.Hom
  open ≈.≈syntax {S = (F.F-ob (Colim D))}

rinv : ∀ x → Colim (F̃ ∘ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
rinv (i , (l , f)) = begin
  ψ₀ (ϕ₀ (i , (l , f)))
    ≈⟨ refl ⟩
  ψ₀ (l , g)
    ≈⟨ ≈lstage 𝟘 ≈leaf ⟩
  𝟘 , (l , h)
    ≈⟨ ≈lstep (𝟘≤t i) (l , h) ⟩
  i , (l , λ b → weaken 𝟘 i (𝟘≤t i) (h b))
    ≈⟨ ≡→≈ (Colim (F̃ ∘ D)) (≡.cong (λ ○ → i , (l , ○)) (funExt (λ ()))) ⟩
  i , (l , f) ∎
  where
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}
  g : ⊥* → ⟨ Colim D ⟩
  g ()
  h : ⊥* → ⟨ D.D-ob 𝟘 ⟩
  h ()
rinv (i , (n , g)) = begin
  ψ₀ (ϕ₀ (i , (n , g)))
    ≈⟨ refl ⟩
  ψ₀ (n , (λ b → i , g b))
    ≈⟨ refl ⟩
  suc i , n , (λ b → weaken i (suc i) (<→≤ (<suc i)) (g b))
    ≈⟨ ≈lsym (≈lstep (<→≤ (<suc i)) (n , g)) ⟩
  i , (n , g) ∎
  where
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}

cocontinuous : Cocontinuous F̃ D
cocontinuous = ∣ iso ∣
  where
  iso : ≈.Iso (Colim (F̃ ∘ D)) (F.F-ob (Colim D))
  iso = record
    { ⟦_⟧ = ϕ₀
    ; ⟦_⟧⁻¹ = ψ₀
    ; cong = ϕ-cong
    ; cong⁻¹ = ψ-cong
    ; linv = linv
    ; rinv = rinv
    }

