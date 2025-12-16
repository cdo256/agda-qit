module Setoid where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
-- open import Relation.Binary.Bundles public
-- open import Function.Bundles
-- open import Function.Definitions
open import Data.Product
-- open import Relation.Binary.Core
-- open import Relation.Binary.Structures
-- open import Relation.Binary.Definitions
-- open import Data.Product.Function.Dependent.Setoid public
-- open import Data.List.Relation.Binary.Equality.Setoid public
-- open import Function.Indexed.Relation.Binary.Equality public
 
private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level

-- open Setoid public
open import Function.Relation.Binary.Setoid.Equality public using () renaming (_≈_ to _≈⃗_)
open import Relation.Binary.Morphism.Bundles 
-- open import Relation.Binary.PropositionalEquality as ≡


-- A wrapper to lift Prop into Set
record Box {ℓ} (P : Prop ℓ) : Set ℓ where
  constructor box
  field unbox : P

open Box


-- substp : ∀ {A : Set ℓ} (B : A → Prop ℓ') {a1 a2 : A} (p : a1 ≡.≡ a2) → B a1 → B a2
-- substp B p x = subst (λ x → Box (B x)) p (box x) .unbox


-- data Setoid c ℓ : Prop (lsuc (c ⊔ ℓ)) where
--   setoid : Setoid c ℓ → Setoid c ℓ

Rel : ∀ (X : Set ℓ) ℓ' → Set (ℓ ⊔ lsuc ℓ')
Rel X ℓ' = X → X → Prop ℓ'

-- Rel : ∀ (X : Set ℓ) ℓ' → Set (ℓ ⊔ lsuc ℓ')
-- Rel X ℓ' = X → X → Set ℓ'

data ∥_∥ (A : Set ℓ) : Prop ℓ where
  ∣_∣ : A → ∥ A ∥

Trunc₁ : {A : Set ℓ} {ℓ' : Level} → (A → Set ℓ') → (A → Prop ℓ')
Trunc₁ R x = ∥ R x ∥

Trunc₂ : {A : Set ℓ} {ℓ' : Level} → (A → A → Set ℓ') → (A → A → Prop ℓ')
Trunc₂ R x y = ∥ R x y ∥

open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

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

record Setoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

-- open Setoid public

  -- open IsEquivalence isEquivalence public
  --   using (refl; reflexive; isPartialEquivalence)

  -- partialSetoid : PartialSetoid c ℓ
  -- partialSetoid = record
  --   { isPartialEquivalence = isPartialEquivalence
  --   }

  -- open PartialSetoid partialSetoid public
  --   hiding (Carrier; _≈_; isPartialEquivalence)

module ≊syntax {ℓ ℓ'} {S : Setoid ℓ ℓ'} where
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
  private
    module S = Setoid S
    module T = Setoid T
  field
    ⟦_⟧ : S.Carrier → T.Carrier
    cong : ∀ {x y} → x S.≈ y → ⟦ x ⟧ T.≈ ⟦ y ⟧

record SetoidIso {ℓ} {ℓ'} (S T : Setoid ℓ ℓ') : Set (ℓ ⊔ ℓ') where
  private
    module S = Setoid S
    module T = Setoid T
  field
    ⟦_⟧ : S.Carrier → T.Carrier
    ⟦_⟧⁻¹ : T.Carrier → S.Carrier
    cong : ∀ {x y} → x S.≈ y → ⟦ x ⟧ T.≈ ⟦ y ⟧
    cong⁻¹ : ∀ {x y} → x T.≈ y → ⟦ x ⟧⁻¹ S.≈ ⟦ y ⟧⁻¹
    linv : ∀ y → ⟦ ⟦ y ⟧⁻¹ ⟧ T.≈ y
    rinv : ∀ x → ⟦ ⟦ x ⟧ ⟧⁻¹ S.≈ x

_≈S_ : ∀ {ℓ ℓ'} → Rel (Setoid ℓ ℓ') (ℓ ⊔ ℓ')
S ≈S T = ∥ SetoidIso S T ∥
  
module _ {ℓ ℓ'} where
  isEquivalenceSetoidIso : IsEquivalence (_≈S_ {ℓ} {ℓ'})
  isEquivalenceSetoidIso = record
    { refl = isReflexive
    ; sym = isSymmetric
    ; trans = isTransitive
    }
    where
    isReflexive : Reflexive (_≈S_ {ℓ} {ℓ'})
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
    isSymmetric : Symmetric (_≈S_ {ℓ} {ℓ'})
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
    ; _≈_ = _≈S_
    ; isEquivalence = isEquivalenceSetoidIso
    }

-- -- infixr 1 _∘_
-- -- _∘_ : ∀ {c₁ c₂ c₃ ℓ₁ ℓ₂ ℓ₃}
-- --         {A : Setoid c₁ ℓ₁} {B : Setoid c₂ ℓ₂} {C : Setoid c₃ ℓ₃} →
-- --         Func B C → Func A B → Func A C
-- -- f ∘ g = record
-- --   { to   = λ x → f .Func.to (g .Func.to x)
-- --   ; cong = λ x≈y → f .Func.cong (g .Func.cong x≈y)
-- --   }

⟨_⟩ : Setoid ℓ ℓ' → Set ℓ
⟨ S ⟩ = S .Setoid.Carrier
