module Setoid where

open import Prelude
open import Data.Product
 
private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level


Reflexive : ∀ {ℓ'} → {A : Set ℓ} (_≈_ : Rel A ℓ') → Prop (ℓ ⊔ ℓ')
Reflexive _≈_ = ∀ {x} → x ≈ x

Symmetric : ∀ {ℓ'} → {A : Set ℓ} (_≈_ : Rel A ℓ') → Prop (ℓ ⊔ ℓ')
Symmetric _≈_ = ∀ {x y} → x ≈ y → y ≈ x

Transitive : ∀ {ℓ'} → {A : Set ℓ} (_≈_ : Rel A ℓ') → Prop (ℓ ⊔ ℓ')
Transitive _≈_ = ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

record IsEquivalence {ℓ'} {A : Set ℓ} (_≈_ : Rel A ℓ') : Prop (ℓ' ⊔ ℓ) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

record Setoid ℓ ℓ' : Set (lsuc (ℓ ⊔ ℓ')) where
  infix 4 _≈_
  field
    Carrier       : Set ℓ 
    _≈_           : Rel Carrier ℓ'
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

⟨_⟩ : Setoid ℓ ℓ' → Set ℓ
⟨ S ⟩ = S .Setoid.Carrier

module ≈syntax {ℓ ℓ'} {S : Setoid ℓ ℓ'} where
  open Setoid S renaming (Carrier to A)

  infix 1 begin_

  begin_ : ∀ {x y} → x ≈ y → x ≈ y
  begin p = p

  step-≈ : ∀ (x : A) {y z} → y ≈ z → x ≈ y → x ≈ z
  step-≈ _ q p = trans p q
  syntax step-≈ x q p = x ≈⟨ p ⟩ q
  
  infix 3 _∎

  _∎ : ∀ x → x ≈ x
  x ∎ = refl

record SetoidHom {ℓ} {ℓ'} (S T : Setoid ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  module S = Setoid S
  module T = Setoid T
  field
    ⟦_⟧ : S.Carrier → T.Carrier
    cong : ∀ {x y} → x S.≈ y → ⟦ x ⟧ T.≈ ⟦ y ⟧

idHom : ∀ {S : Setoid ℓ ℓ'} → SetoidHom S S
idHom {S} = record
  { ⟦_⟧ = λ x → x
  ; cong = λ p → p }

record SetoidIso {ℓ} {ℓ'} (S T : Setoid ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  module S = Setoid S
  module T = Setoid T
  field
    ⟦_⟧ : S.Carrier → T.Carrier
    ⟦_⟧⁻¹ : T.Carrier → S.Carrier
    cong : ∀ {x y} → x S.≈ y → ⟦ x ⟧ T.≈ ⟦ y ⟧
    cong⁻¹ : ∀ {x y} → x T.≈ y → ⟦ x ⟧⁻¹ S.≈ ⟦ y ⟧⁻¹
    linv : ∀ y → ⟦ ⟦ y ⟧⁻¹ ⟧ T.≈ y
    rinv : ∀ x → ⟦ ⟦ x ⟧ ⟧⁻¹ S.≈ x

SetoidIsoFlip : {S T : Setoid ℓ ℓ'} → SetoidIso S T → SetoidIso T S
SetoidIsoFlip f = record
  { ⟦_⟧ = ⟦_⟧⁻¹
  ; ⟦_⟧⁻¹ = ⟦_⟧
  ; cong = cong⁻¹
  ; cong⁻¹ = cong
  ; linv = rinv
  ; rinv = linv
  }
  where open SetoidIso f

SetoidHom≈ : ∀ {S T : Setoid ℓ ℓ'} (f g : SetoidHom S T) → Prop (ℓ ⊔ ℓ')
SetoidHom≈ {S = S} {T} f g = ∀ {x y} → x S.≈ y → f.⟦ x ⟧ T.≈ g.⟦ y ⟧
  where
  module S = Setoid S
  module T = Setoid T
  module f = SetoidHom f
  module g = SetoidHom g

_≅_ : ∀ {ℓ ℓ'} → Rel (Setoid ℓ ℓ') (ℓ ⊔ ℓ')
S ≅ T = ∥ SetoidIso S T ∥

module _ {ℓ ℓ'} where
  isEquivalenceSetoidIso : IsEquivalence (_≅_ {ℓ} {ℓ'})
  isEquivalenceSetoidIso = record
    { refl = isReflexive
    ; sym = isSymmetric
    ; trans = isTransitive
    }
    where
    isReflexive : Reflexive (_≅_ {ℓ} {ℓ'})
    isReflexive {S} = ∣ S~S ∣
      where
      module S = Setoid S
      S~S : SetoidIso S S
      S~S = record
        { ⟦_⟧ = λ x → x
        ; ⟦_⟧⁻¹ = λ x → x
        ; cong = λ p → p
        ; cong⁻¹ = λ p → p
        ; linv = λ _ → S.refl
        ; rinv = λ _ → S.refl
        }
    isSymmetric : Symmetric (_≅_ {ℓ} {ℓ'})
    isSymmetric {S} {T} ∣ p ∣ = ∣ q ∣
      where
      module S = Setoid S
      module T = Setoid T
      module p = SetoidIso p
      q : SetoidIso T S
      q = record
        { ⟦_⟧ = p.⟦_⟧⁻¹
        ; ⟦_⟧⁻¹ = p.⟦_⟧
        ; cong = p.cong⁻¹
        ; cong⁻¹ = p.cong
        ; linv = p.rinv
        ; rinv = p.linv
        }
    isTransitive : Transitive (Trunc₂ (SetoidIso {ℓ} {ℓ'}))
    isTransitive {S} {T} {U} ∣ p ∣ ∣ q ∣ = ∣ r ∣
      where
      module S = Setoid S
      module T = Setoid T
      module U = Setoid U
      module p = SetoidIso p
      module q = SetoidIso q
      r : SetoidIso S U
      r = record
        { ⟦_⟧ = λ z → q.⟦ p.⟦ z ⟧ ⟧
        ; ⟦_⟧⁻¹ = λ z → p.⟦ q.⟦ z ⟧⁻¹ ⟧⁻¹
        ; cong = λ z → q.cong (p.cong z)
        ; cong⁻¹ = λ z → p.cong⁻¹ (q.cong⁻¹ z)
        ; linv = λ y → U.trans (q.cong (p.linv q.⟦ y ⟧⁻¹)) (q.linv y)
        ; rinv = λ x → S.trans (p.cong⁻¹ (q.rinv p.⟦ x ⟧)) (p.rinv x)
        }

  SetoidSetoid : Setoid (lsuc ℓ ⊔ lsuc ℓ') (ℓ ⊔ ℓ')
  SetoidSetoid = record
    { Carrier = Setoid ℓ ℓ'
    ; _≈_ = _≅_
    ; isEquivalence = isEquivalenceSetoidIso
    }

infixr 1 _∘_
_∘_ : ∀ {A B C : Setoid ℓ ℓ'}
    → SetoidHom B C → SetoidHom A B → SetoidHom A C
f ∘ g = record
  { ⟦_⟧  = λ x → f.⟦ g.⟦ x ⟧ ⟧
  ; cong = λ x≈y → f.cong (g.cong x≈y)
  }
  where
  module f = SetoidHom f
  module g = SetoidHom g

Rel≈ : (S : Setoid ℓ ℓ') → ∀ ℓ'' → Set (lsuc ℓ ⊔ lsuc ℓ'')
Rel≈ {ℓ} S ℓ'' = A → A → Prop (ℓ ⊔ ℓ'')
  where
  open Setoid S renaming (Carrier to A)

record IsPreorder (S : Setoid ℓ ℓ') (_≲_ : Rel≈ S ℓ'') : Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
  module S = Setoid S
  field
    refl  : ∀ {x y} → x S.≈ y → x ≲ y
    trans : Transitive _≲_

isEquiv≡p : ∀ (A : Set ℓ) → IsEquivalence (_≡p_ {A = A})
isEquiv≡p A = record { refl = ∣ refl ∣ ; sym = sym ; trans = trans }
  where
  open _≡_
  sym : Symmetric (Trunc₂ _≡_)
  sym ∣ refl ∣ = ∣ refl ∣
  trans : Transitive (Trunc₂ _≡_)
  trans ∣ refl ∣ ∣ refl ∣ = ∣ refl ∣

≡setoid : ∀ (B : Set ℓ) → Setoid ℓ ℓ
≡setoid B = record
  { Carrier = B
  ; _≈_ = _≡p_
  ; isEquivalence = isEquiv≡p B }
