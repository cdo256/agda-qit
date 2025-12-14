module Colimit where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.Bundles
open import Function.Bundles
open import Relation.Binary.Core
open import Relation.Binary.Structures
open import Data.Product.Function.Dependent.Setoid 
open import Relation.Binary.Morphism.Bundles 
open import Setoid as S

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

module _ {ℓI} {ℓI'} {ℓ≤} {ℓB} {ℓB'}
  {I : Setoid ℓI ℓI'}
  {_≤_ : Rel (I .Setoid.Carrier) ℓ≤}
  (isPreorder : IsPreorder (I .Setoid._≈_) _≤_)
  (B : Set ℓB)
  where
  open import Function.Relation.Binary.Setoid.Equality using () renaming (_≈_ to _≈⃗_)
  open import Data.List.Relation.Binary.Equality.Setoid 
  open import Function.Construct.Identity using () renaming (function to identity)
  import Relation.Binary.PropositionalEquality as ≡

  record Diagram : Set (ℓ≤ ⊔ ℓI ⊔ (Level.suc ℓB) ⊔ (Level.suc ℓB')) where
    open IsPreorder isPreorder renaming (reflexive to ≤refl; trans to ≤trans) 
    open Setoid I using () renaming (Carrier to Î)
    module I = Setoid I
    field
      D-ob : ∀ (i : Î)
           → Setoid ℓB ℓB'
      D-mor : ∀ {i j} → (p : i ≤ j)
            → Func (D-ob i) (D-ob j)
      D-id : ∀ {i : Î} → _≈⃗_ (D-ob i) (D-ob i)
                        (D-mor (≤refl (I.reflexive ≡.refl)))
                        (identity (D-ob i))
      D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
             → _≈⃗_ (D-ob i) (D-ob k) (D-mor (≤trans p q)) (D-mor q S.∘ D-mor p)

  module Colim (P : Diagram) where
    open import Data.Product
    open Diagram P renaming (D-ob to P̂)
    open Setoid renaming (Carrier to ⟨_⟩)

    Pf : ∀ {i j} (p : i ≤ j) → (⟨ P̂ i ⟩ → ⟨ P̂ j ⟩)
    Pf p = D-mor p .Func.to

    ≈j : ∀ i → (x y : ⟨ P̂ i ⟩) → Set _
    ≈j i x y = x ≈' y
      where open Setoid (P̂ i) renaming (_≈_ to _≈'_)
    syntax ≈j i x y = x ≈[ i ] y

    Colim₀ : Set (ℓI ⊔ ℓB)
    Colim₀ = Σ[ i ∈ ⟨ I ⟩ ] ⟨ P̂ i ⟩
    data _≈ˡ_ : Colim₀ → Colim₀ → Set (ℓ≤ ⊔ ℓI ⊔ ℓB ⊔ ℓB') where
      ≈lstage : ∀ i → {x x' : ⟨ P̂ i ⟩} → x ≈[ i ] x' → (i , x) ≈ˡ (i , x')
      ≈lstep : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩)
             → (i , x) ≈ˡ (j , Pf p x)
      ≈lsym : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
      ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u 

    equiv : IsEquivalence _≈ˡ_
    equiv = record
      { refl = λ {(i , x)} → ≈lstage i (P̂ i .refl)
      ; sym = ≈lsym
      ; trans = ≈ltrans }


    Colim : Setoid (ℓI ⊔ ℓB) (ℓI ⊔ ℓ≤ ⊔ ℓB ⊔ ℓB')
    Colim = record
      { Carrier = Colim₀
      ; _≈_ = _≈ˡ_
      ; isEquivalence = equiv }

    -- All cocones for this diagram live in the same (ℓ, ℓ') universe
    record Cocone : Set (lsuc (ℓ≤ ⊔ ℓB' ⊔ ℓB ⊔ ℓI)) where
      field
        Apex : Setoid (ℓI ⊔ ℓB) (ℓI ⊔ ℓ≤ ⊔ ℓB ⊔ ℓB')
        inj  : ∀ i → Func (P̂ i) Apex 
        commutes : ∀ {i j} (p : i ≤ j) → _≈⃗_ (P̂ i) Apex (inj i) (inj j ∘ D-mor p) 
    open Cocone

    -- The canonical cocone into the colimit
    LimitCocone : Cocone
    LimitCocone = record
      { Apex = Colim
      ; inj = λ i → record { to = λ x → i , x ; cong = ≈lstage i }
      ; commutes = λ p x → ≈lstep p x }

    -- Morphisms of cocones
    record ColimMorphism (C C' : Cocone) : Set (ℓI ⊔ ℓ≤ ⊔ ℓB ⊔ ℓB') where
      field
        apexHom  : Func (C .Apex) (C' .Apex)
        commutes : ∀ i → _≈⃗_ (P̂ i) (C' .Apex)(apexHom ∘ C .inj i)
                       (C' .inj i)

    open ColimMorphism

    record isLimitingCocone (C : Cocone) : Set (lsuc ℓI ⊔ lsuc ℓ≤ ⊔ lsuc ℓB ⊔ lsuc ℓB') where
      field
        mor : ∀ C' → ColimMorphism C C'
        unique : ∀ C' → (F : ColimMorphism C C')
               → _≈⃗_ (C .Apex) (C' .Apex) (F .apexHom) (mor C' .apexHom)        
               
    open isLimitingCocone 

 
    module IsLimitingCocone (C' : Cocone) where
      open Cocone C'
      module C' = Setoid (C' .Apex)

      private
        f : ⟨ Colim ⟩ → ⟨ C' .Apex ⟩
        f (i , x) = C' .inj i .Func.to x

      isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y)
           →    C' .inj i .Func.to x 
           C'.≈ C' .inj j .Func.to y 
      isRespecting (≈lstage i x≈y) = C' .inj i .Func.cong x≈y
      isRespecting (≈lstep p x) = C' .commutes p x
      isRespecting (≈lsym r) = C'.sym (isRespecting r)
      isRespecting (≈ltrans r s) = C'.trans (isRespecting r) (isRespecting s)

      F : ColimMorphism LimitCocone C'
      F .apexHom .Func.to = f
      F .apexHom .Func.cong = isRespecting
      F .commutes i x = C'.reflexive ≡.refl 

      unq : (G : ColimMorphism LimitCocone C')
          → ∀ x → G .apexHom .Func.to x C'.≈ f x       
      unq G (i , x) = G .commutes i x

    isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
    isLimitingCoconeLimitCocone = record
      { mor = F
      ; unique = unq
      }
      where open IsLimitingCocone
