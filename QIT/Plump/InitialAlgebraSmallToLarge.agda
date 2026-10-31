open import QIT.Prelude hiding (⊥ˢ)
open import QIT.Prop hiding (⊥; _∨_)
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.InitialAlgebraSmallToLarge
  ⦃ pathElim* : PathElim ⦄       
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  where

import QIT.Plump.AlgebraSmall S P as AS
import QIT.Plump.Algebra S P as AL

IAS→IAL
  : AS.InitialExtensionalPlumpOrdinals
  → AL.InitialExtensionalPlumpOrdinals
IAS→IAL IAS = record
  { Zᴬe = Zᴬe
  ; recZᴬ = recZᴬ
  ; rec!Zᴬ = rec!Zᴬ }
  where
  module IAS = AS.InitialExtensionalPlumpOrdinals IAS
  open IAS using (Z; _<_; _≤_)
  sup : Σ S (λ s → P s → Z) → Z
  sup (s , f) = IAS.sup ((AS.ιˢ s) , λ { (AS.ιᵖ s i) → f i })
  sup≤ : ∀ {s f α} → (∀ i → f i < α) → sup (s , f) ≤ α
  sup≤ p = IAS.sup≤ λ { (AS.ιᵖ _ i) → p i }
  <sup : ∀ {s f} → ∀ i {α} → α ≤ f i → α < sup (s , f)
  <sup i p = IAS.<sup (AS.ιᵖ _ i) p

  C<→≤< : ∀ {α β} → α < β → Prop (ℓS ⊔ ℓP)
  C<→≤< {α} {β} _ = α ≤ β

  C<→≤≤ : ∀ {α β} → α ≤ β → Prop (ℓS ⊔ ℓP)
  C<→≤≤ {α} {β} _ =
    ∀ {s : AS.Sᶻ} (f : AS.Pᶻ s → Z) (i : AS.Pᶻ s)
    → β ≡ f i
    → α ≤ IAS.sup (s , f)

  <→≤-sup≤ᴰ
    : ∀ {s : AS.Sᶻ} {f : AS.Pᶻ s → Z} {α}
        (p : ∀ i → f i < α)
    → (∀ i → C<→≤< (p i))
    → C<→≤≤ (IAS.sup≤ p)
  <→≤-sup≤ᴰ {f = f} p ih g i α≡gi =
    IAS.sup≤ λ j →
      IAS.<sup i (substp (λ β → f j ≤ β) α≡gi (ih j))

  <→≤-<supᴰ
    : ∀ {s : AS.Sᶻ} {f : AS.Pᶻ s → Z} {α}
        (i : AS.Pᶻ s) (p : α ≤ f i)
    → C<→≤≤ p
    → C<→≤< (IAS.<sup i p)
  <→≤-<supᴰ {f = f} i p ih = ih f i ≡.refl

  <→≤D : AS.Displayed IAS.Zᴬ
  <→≤D = AS.RelationDisplayed IAS.Zᴬ
    C<→≤< C<→≤≤ <→≤-sup≤ᴰ <→≤-<supᴰ

  <→≤E : AS.Elim <→≤D
  <→≤E = IAS.elimZᴬ <→≤D
    (AS.RelationDisplayed-extensional IAS.Zᴬe
      C<→≤< C<→≤≤ <→≤-sup≤ᴰ <→≤-<supᴰ)

  <→≤ : ∀ {α β} → α < β → α ≤ β
  <→≤ = AS.Elim.<ᴱ <→≤E

  data _<'_ : Z → Z → Prop (ℓS ⊔ ℓP)
  data _≤'_ : Z → Z → Prop (ℓS ⊔ ℓP)
  data _<'_ where
    ι< : ∀ {α β} → α < β → α <' β
    <≤' : {α β γ : Z} → β ≤' γ → α <' β → α <' γ
    ≤<' : {α β γ : Z} → β <' γ → α ≤' β → α <' γ
    <<' : {α β γ : Z} → β <' γ → α <' β → α <' γ
    <sup' : ∀ {s f} → ∀ i {α} → α ≤' f i → α <' IAS.sup (s , f)

  data _≤'_ where
    ι≤ : ∀ {α β} → α ≤ β → α ≤' β
    ≤≤' : {α β γ : Z} → β ≤' γ → α ≤' β → α ≤' γ
    <→≤' : {α β γ : Z} → α <' β → α ≤' β
    sup≤' : ∀ {s f α} → (∀ i → f i <' α) → IAS.sup (s , f) ≤' α

  B : AS.PlumpAlgebra
  B = record
    { Z = Z
    ; sup = IAS.sup
    ; _<_ = _<'_
    ; _≤_ = _≤'_
    ; sup≤ = sup≤'
    ; <sup = <sup' }

  <'→< : ∀ {α β} → α <' β → α < β
  ≤'→≤ : ∀ {α β} → α ≤' β → α ≤ β

  <'→< {α} {β} (ι< p) = p
  <'→< {α} {β} (<≤' p q) = {!!}
  <'→< {α} {β} (≤<' p q) = {!!}
  <'→< {α} {β} (<<' p q) = {!!}
  <'→< {α} {β} (<sup' i x) = {!!}
  ≤'→≤ {α} {β} p = {!!}

  B→I : AS.PlumpHom B IAS.Zᴬ
  B→I = record
    { Z = λ z → z
    ; sup = λ s f → ≡.refl
    ; _<_ = {!!}
    ; _≤_ = {!!} }

  Zᴬe : AL.ExtensionalPlumpAlgebra
  Zᴬe = record
    { Zᴬ = record
      { Z = IAS.Z
      ; sup = sup
       ; _<_ = IAS._<_
       ; _≤_ = IAS._≤_
       ; sup≤ = sup≤
       ; <sup = <sup
       ; ≤≤ = {!!}
       ; ≤< = {!!}
       ; <≤ = {!!}
       ; << = {!!}
       ; <→≤ = {!!}
       ; ≤refl = {!!}
       ; _∨ᶻ_ = {!!}
       ; ∨ᶻ-l< = {!!}
       ; ∨ᶻ-r< = {!!}
       ; ∨ᶻ≤ = {!!}
       ; ∨ᶻ-flip = {!!}
       ; ⊥ᶻ = {!!}
       ; ⊥ᶻ≤ = {!!}
       ; iswf< = {!!}
       }
     ; antisym = {!!} }
  recZᴬ : (Zᴬ' : AL.ExtensionalPlumpAlgebra) →
           AL.PlumpHom (AL.ExtensionalPlumpAlgebra.Zᴬ Zᴬe)
           (AL.ExtensionalPlumpAlgebra.Zᴬ Zᴬ')
  rec!Zᴬ : (Zᴬ' : AL.ExtensionalPlumpAlgebra)
            (f
             : AL.PlumpHom (AL.ExtensionalPlumpAlgebra.Zᴬ Zᴬe)
               (AL.ExtensionalPlumpAlgebra.Zᴬ Zᴬ')) →
            f AL.≈ᵖ recZᴬ Zᴬ'
