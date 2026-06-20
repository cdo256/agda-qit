open import QIT.Prelude
open import QIT.Prop
open import QIT.QW.Signature

module QIT.QW.Subclasses {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  where

open Sig sig

-- import QIT.Plump.Algebra as Plump
-- import QIT.Plump.W.Base as PlumpW
-- import QIT.Plump.Properties as PlumpP

open import QIT.Plump.W.Base S P as Z

open import QIT.Nat
open import QIT.Relation.Subset
open import QIT.Container.Base
open import QIT.Container.Properties
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Setoid
open import QIT.QW.W S P
open import QIT.QW.Equation S P ℓV
open import QIT.Functor.Base

expr→Z : {V : Set ℓV} → Expr V → Z
expr→Z (W.sup (inj₁ v , f)) = ⊥ᶻ
expr→Z (W.sup (inj₂ s , f)) = Z.sup (ιˢ s , λ i → expr→Z (f i))

_≤ᴱ_ : {V : Set ℓV} → Expr V → Z → Prop ℓA
e ≤ᴱ α = expr→Z e Z.≤ α

record OccurrenceAtDepth {V : Set ℓV} (v : V) (e : Expr V) (n : ℕ) : Set (ℓS ⊔ ℓP ⊔ ℓV) where
  field
    p : Path e
    len : pathLength p ≡ n
    lookup : getShape (pathLookup p) ≡ inj₁ v

OccursAtDepth : {V : Set ℓV} (v : V)
              → (e : Expr V) (n : ℕ)
              → Prop (ℓS ⊔ ℓP ⊔ ℓV)
OccursAtDepth v e n = ∥ OccurrenceAtDepth v e n ∥

record DepthPreservingEquation (E : Equation) : Prop (ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓV) where
  module E = Equation E
  field
    var : ∀ (v : E.V) (n : ℕ)
        → OccursAtDepth v E.lhs n ⇔ OccursAtDepth v E.rhs n
    eq : ∀ (α : Z) → E.lhs ≤ᴱ α ⇔ E.rhs ≤ᴱ α

record DepthPreservingSig : Prop (ℓE ⊔ ℓA ⊔ ℓS ⊔ ℓP ⊔ ℓV) where
  field
    dp : ∀ (e : E) → DepthPreservingEquation (Ξ e)

LocalEquation : (E : Equation) → (α : Z) → Prop ℓA
LocalEquation E α = E.lhs ≤ᴱ α ∧ E.rhs ≤ᴱ α
  where
  module E = Equation E
