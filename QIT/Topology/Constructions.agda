module QIT.Topology.Constructions where

open import QIT.Prelude
open import QIT.Prop
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import QIT.Relation.Subset
open import QIT.Topology.Subset
open import QIT.Topology.Base
open import QIT.Relation.SetQuotient

⨆ : ∀ {ℓJ ℓ𝓤 ℓ𝓟 ℓ𝓞}
   → (J : Set ℓJ)
   → (J → Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
   → Space (ℓJ ⊔ ℓ𝓤) ℓ𝓟 (ℓJ ⊔ ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞)
⨆ J Aᴶ =
  FreeSpace _ ⨆A 𝓞⨆
  where
  open Space
  ⨆A : Set _
  ⨆A = Σ J λ j → ⟨ Aᴶ j ⟩
  𝓞⨆ : 𝓟 _ ⨆A → Prop _
  𝓞⨆ X = ∀ j → 𝓞 (Aᴶ j) (λ x → X (j , x))

⨅ : ∀ {ℓJ ℓ𝓤 ℓ𝓟 ℓ𝓞}
   → (J : Set ℓJ)
   → (J → Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
   → Space (ℓJ ⊔ ℓ𝓤) (ℓJ ⊔ ℓ𝓟) (lsuc ℓJ ⊔ ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞)
⨅ {ℓJ} {ℓ𝓤} {ℓ𝓟} {ℓ𝓞} J Aᴶ =
  FreeSpace (ℓJ ⊔ ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞) ⨅A 𝓞⨅
  where
  open Space
  
  ⨅A : Set (ℓJ ⊔ ℓ𝓤)
  ⨅A = ∀ j → ⟨ Aᴶ j ⟩
  
  data 𝓞⨅ : 𝓟 (ℓJ ⊔ ℓ𝓟) ⨅A
           → Prop (ℓJ ⊔ ℓ𝓤 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞)
    where
    intro⨅ : (Xᴶ : ∀ j → 𝓟 ℓ𝓟 ⟨ Aᴶ j ⟩)
            → (𝓞X : ∀ j → 𝓞 (Aᴶ j) (Xᴶ j))
            → 𝓞⨅ (⨅ˢ J λ j x → Xᴶ j x)

_⊔ᵀ_
   : ∀ {ℓ𝓤 ℓ𝓥 ℓ𝓟 ℓ𝓞 ℓ𝓞'}
   → (X : Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
   → (Y : Space ℓ𝓥 ℓ𝓟 ℓ𝓞')
   → Space (ℓ𝓤 ⊔ ℓ𝓥) ℓ𝓟 (ℓ𝓤 ⊔ ℓ𝓥 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞 ⊔ ℓ𝓞')
_⊔ᵀ_ {ℓ𝓤} {ℓ𝓥} {ℓ𝓟} {ℓ𝓞} {ℓ𝓞'} X Y =
  ⨆ Bool (if_then LiftSpace ℓ𝓥 ℓ𝓞' X else LiftSpace ℓ𝓤 ℓ𝓞 Y)

_⊓ᵀ_
   : ∀ {ℓ𝓤 ℓ𝓥 ℓ𝓟 ℓ𝓞 ℓ𝓞'}
   → (X : Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
   → (Y : Space ℓ𝓥 ℓ𝓟 ℓ𝓞')
   → Space (ℓ𝓤 ⊔ ℓ𝓥) ℓ𝓟 (ℓ𝓤 ⊔ ℓ𝓥 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞 ⊔ ℓ𝓞')
_⊓ᵀ_ {ℓ𝓤} {ℓ𝓥} {ℓ𝓟} {ℓ𝓞} {ℓ𝓞'} X Y =
  ⨅ Bool (if_then LiftSpace ℓ𝓥 ℓ𝓞' X else LiftSpace ℓ𝓤 ℓ𝓞 Y)

_/ᵀ_
   : ∀ {ℓ𝓤 ℓ𝓟 ℓ𝓞}
   → (X : Space ℓ𝓤 ℓ𝓟 ℓ𝓞)
   → (A : 𝓟 ℓ𝓟 (X .Space.𝓤))
   → Space (ℓ𝓤 ⊔ ℓ𝓟) ℓ𝓟 (ℓ𝓤 ⊔ ℓ𝓟 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞)
_/ᵀ_ {ℓ𝓤} {ℓ𝓟} {ℓ𝓞} X A =
  FreeSpace ℓ𝓞 𝓤' 𝓞'
  where
  module X = Space X
  R : X.𝓤 → X.𝓤 → Prop ℓ𝓟
  R x y = x ∈ A ∧ y ∈ A
  𝓤' : Set (ℓ𝓤 ⊔ ℓ𝓟)
  𝓤' = X.𝓤 / R 
  𝓞' : 𝓟 ℓ𝓟 𝓤' → Prop _ 
  𝓞' A = X.𝓞 (λ x → [ x ] ∈ A)

_∨ᵀ_
   : ∀ {ℓ𝓤 ℓ𝓥 ℓ𝓟 ℓ𝓞 ℓ𝓞'}
   → (X : Space· ℓ𝓤 ℓ𝓟 ℓ𝓞)
   → (Y : Space· ℓ𝓥 ℓ𝓟 ℓ𝓞')
   → Space· {!ℓ𝓤 ⊔ ℓ𝓥!} {!ℓ𝓟!} {!ℓ𝓤 ⊔ ℓ𝓥 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞 ⊔ ℓ𝓞'!}
_∨ᵀ_ {ℓ𝓤} {ℓ𝓥} {ℓ𝓟} {ℓ𝓞} {ℓ𝓞'} (X , x) (Y , y) =
  Z , {!!}   
  where
  Z : Space (ℓ𝓤 ⊔ ℓ𝓥 ⊔ ℓ𝓟) ℓ𝓟
       (ℓ𝓤 ⊔ ℓ𝓥 ⊔ ℓ𝓟 ⊔ lsuc ℓ𝓟 ⊔ (ℓ𝓤 ⊔ ℓ𝓥 ⊔ lsuc ℓ𝓟 ⊔ ℓ𝓞 ⊔ ℓ𝓞'))
  Z = (X ⊔ᵀ Y) /ᵀ [ (true , lift x) ∷ (false , lift y) ∷ [] ]ᴾ
