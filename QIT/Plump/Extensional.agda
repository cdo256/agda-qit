open import QIT.Prelude
open import QIT.Prop hiding (⊥; _∨_)
open import QIT.Container.Base using (⟦_◁_⟧) renaming (sup to supᵂ)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset
open import QIT.Plump.Algebra

module QIT.Plump.Extensional
  ⦃ pathElim* : PathElim ⦄       
  ⦃ funExt* : FunExt ⦄ 
  ⦃ epo* : ExtensionalPlumpOrdinals ⦄
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  where

open FunExt funExt*

module Z₀ where
  open import QIT.Plump.W S P public
  open import QIT.Plump.Properties Zᴬ
    hiding (sucᶻ; <sucᶻ; child≤; ≤cong; ≤p; isPreorder-≤) public

open ExtensionalPlumpOrdinals epo*
open ExtensionalPlumpAlgebra (Zᴬe S P) public
open import QIT.Plump.Properties Zᴬ public

[_]ᶻ : Z₀.Z → Z
[ supᵂ (Z₀.⊥ₛ , f) ]ᶻ = ⊥ᶻ
[ supᵂ (Z₀.∨ₛ , f) ]ᶻ =
     [ f (inj₁ tt*) ]ᶻ
  ∨ᶻ [ f (inj₂ tt*) ]ᶻ
[ supᵂ (Z₀.ιₛ s , f) ]ᶻ =
  sup (s , λ i → [ f i ]ᶻ)
ιᶻ-factors : ∀ x → [ Z₀.ιᶻ x ]ᶻ ≡ ιᶻ x
ιᶻ-factors (supᵂ (s , f)) =
  ≡.cong (λ ○ → sup (s , ○))
         (funExt λ i → ιᶻ-factors (f i))
≤[_]ᶻ : ∀ {α β : Z₀.Z}
      → α Z₀.≤ β → [ α ]ᶻ ≤ [ β ]ᶻ
<[_]ᶻ : ∀ {α β : Z₀.Z}
      → α Z₀.< β → [ α ]ᶻ < [ β ]ᶻ
<[_]ᶻ {α} {supᵂ (Z₀.⊥ₛ , ξ)} (Z₀.<sup () α≤ξi)
<[_]ᶻ {α} {supᵂ (Z₀.∨ₛ , ξ)} (Z₀.<sup (inj₁ tt*) α≤ξ₁) =
  <≤ ∨ᶻ-l< ≤[ α≤ξ₁ ]ᶻ
<[_]ᶻ {α} {supᵂ (Z₀.∨ₛ , ξ)} (Z₀.<sup (inj₂ tt*) α≤ξ₂) =
  <≤ ∨ᶻ-r< ≤[ α≤ξ₂ ]ᶻ
<[_]ᶻ {α} {supᵂ (Z₀.ιₛ s , ξ)} (Z₀.<sup i α≤ξi) =
  <sup i ≤[ α≤ξi ]ᶻ
≤[_]ᶻ {supᵂ (Z₀.⊥ₛ , ξ)} {β} _ = ⊥ᶻ≤
≤[_]ᶻ {supᵂ (Z₀.∨ₛ , ξ)} {β} (Z₀.sup≤ ξ<β) =
  ∨ᶻ≤ <[ ξ<β (inj₁ tt*) ]ᶻ <[ ξ<β (inj₂ tt*) ]ᶻ
≤[_]ᶻ {supᵂ (Z₀.ιₛ s , ξ)} {β} (Z₀.sup≤ ξ<β) =
  sup≤ (λ i → <[ ξ<β i ]ᶻ)

ιᶻ≤ιᶻ : ∀ x y
  → Z₀.ιᶻ x Z₀.≤ Z₀.ιᶻ y 
  → ιᶻ x ≤ ιᶻ y
ιᶻ≤ιᶻ x y p =
  ≡.substp₂ _≤_
    (ιᶻ-factors x)
    (ιᶻ-factors y)
    ≤[ p ]ᶻ

ιᶻ≤≥ιᶻ : ∀ x y
  → Z₀.ιᶻ x Z₀.≤≥ Z₀.ιᶻ y 
  → ιᶻ x ≤ ιᶻ y ∧ ιᶻ y ≤ ιᶻ x
ιᶻ≤≥ιᶻ x y (∧i p , q) = ∧i ιᶻ≤ιᶻ x y p , ιᶻ≤ιᶻ y x q

≤≥→≡ : ∀ {α β} → α ≤ β ∧ β ≤ α → α ≡ β
≤≥→≡ (∧i p , q) = antisym p q
