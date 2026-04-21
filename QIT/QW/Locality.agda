open import QIT.Prelude
open import QIT.Prop
open import QIT.QW.Signature

module QIT.QW.Locality {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where
open Sig sig

open import Data.Nat.Base hiding (_⊔_)
open import QIT.Relation.Subset
open import QIT.Container.Base
open import QIT.Container.Properties
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓV)
open import QIT.Setoid
open import QIT.QW.W S P
open import QIT.QW.Equation S P ℓV
open import QIT.QW.Stage sig
open import QIT.Functor.Base
open import QIT.Plump.Postulated S P as Z

record OccurrenceAtDepth {V : Set ℓV} (v : V) (e : Expr V) (n : ℕ) : Set (ℓS ⊔ ℓP ⊔ ℓV) where
  field
    p : Path e
    len : pathLength p ≡ n
    lookup : getShape (pathLookup p) ≡ inj₁ v

OccursAtDepth : {V : Set ℓV} (v : V)
              → (e : Expr V) (n : ℕ)
              → Prop (ℓS ⊔ ℓP ⊔ ℓV)
OccursAtDepth v e n = ∥ OccurrenceAtDepth v e n ∥

record DepthPreservingEquation (E : Equation) : Prop (ℓS ⊔ ℓP ⊔ ℓV) where
  module E = Equation E
  field
    var : ∀ (v : E.V) (n : ℕ)
        → OccursAtDepth v E.lhs n ⇔ OccursAtDepth v E.rhs n
    eq : ∀ (α : Z) → E.lhs ≤ᴱ α ⇔ E.rhs ≤ᴱ α

LocalEquation : (E : Equation) → (α : Z) → Prop (ℓS ⊔ ℓP)
LocalEquation E α = E.lhs ≤ᴱ α ∧ E.rhs ≤ᴱ α
  where
  module E = Equation E

DepthPreservingSig : Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
DepthPreservingSig = ∀ (e : E) → DepthPreservingEquation (Ξ e)

DepthPreserving : Prop (ℓS ⊔ ℓP ⊔ ℓE ⊔ lsuc ℓV)
DepthPreserving = ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≡ ιᶻ (t̂ .fst)


DPSig→DP : DepthPreservingSig → DepthPreserving
DPSig→DP dp (≈pcong a μ f g r) =
  ≡.cong (λ ○ → Z.sup (ιˢ a , ○)) (≡.funExt λ i → DPSig→DP dp (r i))
DPSig→DP dp (≈psat e ϕ l≤α r≤α) = {!!}
  where
  open DepthPreservingEquation (dp e)
  l≤r : ιᶻ (lhs' e ϕ) Z.≤ ιᶻ (rhs' e ϕ)

DPSig→DP dp ≈prefl = ≡.refl
DPSig→DP dp (≈psym p) = ≡.sym (DPSig→DP dp p)
DPSig→DP dp (≈ptrans p q) = ≡.trans (DPSig→DP dp p) (DPSig→DP dp q)
DPSig→DP dp (≈pweaken α≤β p) = DPSig→DP dp p
