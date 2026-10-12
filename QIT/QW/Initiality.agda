{-# OPTIONS --type-in-type #-}
open import QIT.Prelude
open import QIT.QW.Signature
open import QIT.Plump.Algebra
open import QIT.Relation.SetQuotient
open import QIT.Function.Base
open import QIT.Functor.Base
open import QIT.Container.Base
open import QIT.Setoid

module QIT.QW.Initiality
  ⦃ pathElim* : PathElim ⦄
  ⦃ a!c* : A!C ⦄
  ⦃ funExt* : FunExt ⦄ 
  ⦃ propExt* : PropExt ⦄ 
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓP ℓE ℓV}
  (sig : Sig ℓS ℓP ℓE ℓV)
  (Zᴬ  : PlumpAlgebra (sig .Sig.S) (sig .Sig.P))
  where

open Sig sig
module Z = PlumpAlgebra Zᴬ
open import QIT.Plump.Properties Zᴬ
open import QIT.QW.Diagram sig Zᴬ
open import QIT.Container.StrictFunctor S P (ℓS ⊔ ℓP ⊔ ℓE ⊔ ℓV)
open import QIT.QW.Stage sig Zᴬ
module F = Functor F

module _
  (cc : FD*/ ≅ˢ F.ob D*/)
  where
  module cc = _≅ˢ_ cc

  open import QIT.QW.Algebra sig
  open import QIT.Algebra.Base
  open import QIT.Colimit.Base ≤p _ _ D̃/
  
  data R : ⟨ D* ⟩ → ⟨ D* ⟩ → Prop _ where
    Rcolim : ∀ x y → x ≈ˡ y → R x y
    Rweaken : ∀ {α β} (p : α Z.≤ β) (x : S̃/ α) → R (α , x) (β , dweaken/ p x)
    Rσ : ∀ {α β} (p : α Z.≤ β) (s : S) (f : P s → S̃/ α)
      → R (β , let u = sup (s , λ i → {!f i!}) in {!!}) (α , {!!})

  D*/R : {!D* / R!}

  qw : Record
  qw = record
    { Xα = record
      { alg = mkAlg D*/ ρ
      ; sat = {!!} }
    ; initial = {!!} }
    where
    ε₀' : (α : Z.Z) → ⟦ S ◁ P ⟧ (S₀ α) → S₀ (sucᶻ α)
    ε₀' α (s , f) = sup (s , λ i → f i .fst) , Z.sup≤ (λ i → Z.<≤ (<sucᶻ α) (f i .snd))
    ε₀ : ⟨ FD* ⟩ → ⟨ D* ⟩
    ε₀ (α , s , f) = sucᶻ α , (S̃ (sucᶻ α) ⊢[ ε₀' α (s , λ i → {!!} , {!!}) ])
    ε-cong : {!!}
    ε-cong = {!!}
    ε : FD*/ → D*/
    ε = {!!}
    ρ : F.ob D*/ → D*/
    ρ x = ε (cc.from x)
    sup₀ : F.ob ⟨ D* ⟩ → ⟨ D* ⟩
    sup₀ (s , f) = α , {!!}
      where
      α : Z.Z
      α = Z.sup (s , λ i → f i .proj₁)
  
