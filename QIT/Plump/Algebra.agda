open import QIT.Prelude
open import QIT.Prop hiding (⊥; _∨_)
open import QIT.Container.Base as W using (⟦_◁_⟧)
open import QIT.Relation.Binary using (WellFounded)
open import QIT.Relation.Subset

module QIT.Plump.Algebra
  ⦃ pathElim* : PathElim ⦄       
  where

record PlumpAlgebra
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where

  infix 4 _≤_ _<_
  infixl 10 _∨ᶻ_

  private
    T = W.W S P

  field
    Z : Set (ℓS ⊔ ℓP)
    sup : Σ S (λ s → P s → Z) → Z
    _<_ : Z → Z → Prop (ℓS ⊔ ℓP)
    _≤_ : Z → Z → Prop (ℓS ⊔ ℓP)

    sup≤ : {s : S} {f : P s → Z} {α : Z}
          → (∀ i → f i < α)
          → sup (s , f) ≤ α
    <sup : {s : S} {f : P s → Z}
          → (i : P s) → {α : Z}
          → α ≤ f i
          → α < sup (s , f)

    ≤≤ : {α β γ : Z} → β ≤ γ → α ≤ β → α ≤ γ
    ≤< : {α β γ : Z} → β ≤ γ → α < β → α < γ
    <≤ : {α β γ : Z} → β < γ → α ≤ β → α < γ
    << : {α β γ : Z} → β < γ → α < β → α < γ
    <→≤ : {α β : Z} → α < β → α ≤ β

    ≤refl : ∀ α → α ≤ α

    _∨ᶻ_ : Z → Z → Z
    ∨ᶻ-l< : ∀ {α β} → α < (α ∨ᶻ β)
    ∨ᶻ-r< : ∀ {α β} → β < (α ∨ᶻ β)
    ∨ᶻ≤ : ∀ {α β γ} → α < γ → β < γ → (α ∨ᶻ β) ≤ γ
    ∨ᶻ-flip : ∀ {α β} → (β ∨ᶻ α) ≤ (α ∨ᶻ β)

    ⊥ᶻ : Z
    ⊥ᶻ≤ : ∀ {α} → ⊥ᶻ ≤ α

    iswf< : WellFounded _<_

record ExtensionalPlumpAlgebra
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    Zᴬ : PlumpAlgebra S P

  open PlumpAlgebra Zᴬ public

  field
    antisym : ∀ {α β} → α ≤ β → β ≤ α → α ≡ β


record ExtensionalPlumpHom
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  (A B : ExtensionalPlumpAlgebra S P)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module A = ExtensionalPlumpAlgebra A
  module B = ExtensionalPlumpAlgebra B
  field
    Z : A.Z → B.Z
    sup : (s : S)
      → (f : P s → A.Z)
      → Z (A.sup (s , f)) ≡ B.sup (s , λ i → Z (f i))
    _<_ : ∀ {α β} → α A.< β → Z α B.< Z β
    _≤_ : ∀ {α β} → α A.≤ β → Z α B.≤ Z β

record _≈ᵉᵖ_
  {ℓS ℓP} {S : Set ℓS} {P : S → Set ℓP}
  {A B : ExtensionalPlumpAlgebra S P}
  (f g : ExtensionalPlumpHom A B)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  module A = ExtensionalPlumpAlgebra A
  module B = ExtensionalPlumpAlgebra B
  module f = ExtensionalPlumpHom f
  module g = ExtensionalPlumpHom g
  field
    Z : A.Z → B.Z
    sup : (s : S)
      → (f : P s → A.Z)
      → Z (A.sup (s , f)) ≡ B.sup (s , λ i → Z (f i))
    _<_ : ∀ {α β} → α A.< β → Z α B.< Z β
    _≤_ : ∀ {α β} → α A.≤ β → Z α B.≤ Z β

record InitialExtensionalPlumpOrdinals
  {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
  : Set (lsuc ℓS ⊔ lsuc ℓP) where
  field
    Zᴬe : ExtensionalPlumpAlgebra S P
    recZᴬ
      : (Zᴬ' : ExtensionalPlumpAlgebra S P)
      → ExtensionalPlumpHom Zᴬe Zᴬ'
    rec!Zᴬ
      : (Zᴬ' : ExtensionalPlumpAlgebra S P)
      → (f : ExtensionalPlumpHom Zᴬe Zᴬ')
      → f ≈ᵉᵖ recZᴬ Zᴬ'
  open ExtensionalPlumpAlgebra Zᴬe

  open import QIT.Relation.Binary

  A : (δ : Z) → PlumpAlgebra S P
  A δ = record
    { Z = ΣP Z (λ α → (∀ γ → γ < α → γ < δ) → α ≤ δ)
    ; sup = λ (s , f)
      → (sup (s , (λ i → f i .fst)))
      , λ p → sup≤ λ i → p (f i .fst) (<sup i (≤refl _))
    ; _<_ = λ (α , _) (β , _) → α < β
    ; _≤_ = λ (α , _) (β , _) → α ≤ β
    ; sup≤ = sup≤
    ; <sup = λ i p → <sup i p
    ; ≤≤ = ≤≤
    ; ≤< = ≤<
    ; <≤ = <≤
    ; << = <<
    ; <→≤ = <→≤
    ; ≤refl = λ (α , _) → ≤refl α
    ; _∨ᶻ_ = λ (α , pα) (β , pβ) → α ∨ᶻ β , λ p → ∨ᶻ≤ (p α ∨ᶻ-l<) (p β ∨ᶻ-r<)
    ; ∨ᶻ-l< = ∨ᶻ-l<
    ; ∨ᶻ-r< = ∨ᶻ-r<
    ; ∨ᶻ≤ = ∨ᶻ≤
    ; ∨ᶻ-flip = ∨ᶻ-flip
    ; ⊥ᶻ = ⊥ᶻ , λ _ → ⊥ᶻ≤
    ; ⊥ᶻ≤ = ⊥ᶻ≤
    -- ; iswf< = {!!}
    }

  Ae : (δ : Z) → ExtensionalPlumpAlgebra S P
  Ae δ = record { Zᴬ = A δ ; antisym = λ p q → ΣP≡ _ _ (antisym p q) }

  qext : ∀ {α β} → (∀ γ → γ < α → γ < β) → α ≤ β  
  qext {α} {β} = u
    where
    r : ExtensionalPlumpHom Zᴬe (Ae β)
    r = recZᴬ (Ae β)
    module r = ExtensionalPlumpHom r
    q : r.Z α .fst ≡ α
    q = {!!}
    u : ((γ : Z) → γ < α → γ < β) → α ≤ β
    u = substp (λ α → ((γ : Z) → γ < α → γ < β) → α ≤ β) q (r.Z α .snd)
    
      
  ext : ∀ {α β} → (∀ γ → γ < α ⇔ γ < β) → α ≡ β  
  ext {α} {β} p = {!!}
    where
    r : (α : Z) → (∀ γ → γ < α → γ ≤ β) → α ≤ β
    r α p' = {!!}
    q : α ≤ β
    q = wf-rec _<_ iswf< (_≤ β) r α
    
record ExtensionalPlumpOrdinals : Setω where
  field
    Zᴬe : ∀ {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP)
        → InitialExtensionalPlumpOrdinals S P

