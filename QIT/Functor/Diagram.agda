open import QIT.Prelude hiding (ℓD)
open import QIT.Prop
open import QIT.Relation.SetQuotient
open import QIT.Plump.Algebra
open import QIT.Relation.Binary

-- Define staged construction of quotient W-types using plump ordinals.
-- This builds the quotient in stages indexed by ordinals, ensuring that
-- equations are satisfied at each stage. The construction uses diagrams
-- indexed by the plump ordinal order to control the complexity of terms.
module QIT.Functor.Diagram
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓA ℓ≤} {A : Set ℓA} (≤p : Preorder A ℓ≤)
  where

private
  _≤_ = ≤p .proj₁

open FunExt funExt*

open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base using (_≡h_)
open import QIT.Category.Base
open import QIT.Category.Preorder
open import QIT.Category.Setoid
open import QIT.Category.Set
open import QIT.Functor.Base
open import QIT.Functor.Quotient
open import QIT.Functor.Properties
open import QIT.Setoid.Hom 

open SQ

-- Diagram is a functor from a preorder category to setoids
Diagram : ∀ ℓD ℓD' → Set (ℓA ⊔ ℓ≤ ⊔ lsuc ℓD ⊔ lsuc ℓD')
Diagram ℓD ℓD' =
  Functor (PreorderCat A ≤p) (SetoidCat ℓD ℓD')

_/≈ᴰ : ∀ {ℓD ℓD'}
     → Diagram ℓD ℓD'
     → Functor (PreorderCat A ≤p) (SetCat (ℓD ⊔ ℓD'))
D /≈ᴰ = QuotientFunctor ∘ꟳ D

PowerSetoid : ∀ {ℓS ℓS'} → Setoid ℓS ℓS' → Set ℓX → Setoid (ℓS ⊔ ℓX) (ℓS' ⊔ ℓX)
PowerSetoid S X = record
  { Carrier = X → ⟨ S ⟩
  ; _≈_ = λ f g → ∀ x → f x ≈ g x
  ; isEquivalence = record
    { refl = λ _ → refl
    ; sym = λ p _ → sym (p _)
    ; trans = λ p q _ → trans (p _) (q _) } }
  where
  open Setoid S

PowerDiagram : ∀ {ℓX ℓD ℓD'} → Diagram ℓD ℓD' → Set ℓX → Diagram (ℓD ⊔ ℓX) (ℓD' ⊔ ℓX)
PowerDiagram {ℓX} {ℓD} {ℓD'} D X = record
  { ob   = ob
  ; hom  = hom'
  ; id   = λ _ → D.id
  ; comp = λ f g _ → D.comp f g
  ; resp = λ p _ → D.resp p
  }
  where
  module D = Functor D
  ob : A → Setoid (ℓD ⊔ ℓX) (ℓD' ⊔ ℓX)
  ob α = PowerSetoid (D.ob α) X
  hom' : ∀ {α β} (p : Box (α ≤ β)) → ≈.Hom (ob α) (ob β)
  hom' p = record
    { to = λ f x → D.hom p .Hom.to (f x)
    ; cong = λ {f g} q x → D.hom p .Hom.cong (q x) }
