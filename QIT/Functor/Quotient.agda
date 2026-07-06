open import QIT.Prelude hiding (ℓS)
open import QIT.Prop
open import QIT.Relation.SetQuotient
open import QIT.Plump.Algebra
open import QIT.Relation.Binary

-- Define staged construction of quotient W-types using plump ordinals.
-- This builds the quotient in stages indexed by ordinals, ensuring that
-- equations are satisfied at each stage. The construction uses diagrams
-- indexed by the plump ordinal order to control the complexity of terms.
module QIT.Functor.Quotient
  ⦃ a!c* : A!C ⦄ 
  ⦃ pathElim* : PathElim ⦄
  ⦃ funExt* : FunExt ⦄
  ⦃ propExt* : PropExt ⦄
  ⦃ sq* : SetQuotients ⦄
  {ℓS ℓ≈ : Level}
  where

open FunExt funExt*

open import QIT.Setoid
open import QIT.Setoid.Quotient
open import QIT.Set.Base using (_≡h_)
open import QIT.Category.Base
open import QIT.Category.Preorder
open import QIT.Category.Setoid
open import QIT.Category.Set
open import QIT.Functor.Base
open import QIT.Functor.Properties
open import QIT.Setoid.Hom 

module SetoidCat = Category (SetoidCat ℓS ℓ≈)
module SetCat = Category (SetCat (ℓS ⊔ ℓ≈))
hom : ∀ {X Y : Setoid ℓS ℓ≈} → ≈.Hom X Y → X /≈ → Y /≈
hom {X} {Y} p =
  ≈.map X Y p.to p.cong
  where
  module p = ≈.Hom p
id : ∀ {X} → hom (SetoidCat.id {X}) ≡h SetCat.id {X /≈}
id {X} {x} = SQ.elimp X (λ z → hom (SetoidCat.id {X}) z ≡ z) p x
  where
  p : (a : ⟨ X ⟩) → hom (SetoidCat.id {X}) (X ⊢[ a ]) ≡ X ⊢[ a ]
  p a = map-beta X X (λ x → x) (λ p → p) a
comp : ∀ {X Y Z} (f : ≈.Hom X Y) (g : ≈.Hom Y Z)
      → hom (g SetoidCat.∘ f) ≡h hom g SetCat.∘ hom f
comp {X} {Y} {Z} f g {x} =
  SQ.elimp X (λ x → hom (g SetoidCat.∘ f) x ≡ (hom g SetCat.∘ hom f) x) p x
  where
  open ≡.≡-Reasoning
  module f = ≈.Hom f
  module g = ≈.Hom g
  p : ∀ a → hom (g ≈.∘ f) (X ⊢[ a ]) ≡ (hom g SetCat.∘ hom f) (X ⊢[ a ])
  p a = 
    hom (g ≈.∘ f) (X ⊢[ a ])
      ≡⟨ map-beta X Z (λ x → g.to (f.to x))
                      (λ p → g.cong (f.cong p)) a ⟩
    Z ⊢[ g.to (f.to a) ]
      ≡⟨ ≡.sym (map-beta Y Z g.to g.cong (f.to a)) ⟩
    hom g (Y ⊢[ f.to a ])
      ≡⟨ ≡.sym (≡.cong (hom g) (map-beta X Y f.to f.cong a)) ⟩
    hom g (hom f (X ⊢[ a ])) ∎
resp : ∀ {X Y} {f g : ≈.Hom X Y} → f ≈h g → hom f ≡h hom g
resp {X} {Y} {f} {g} p {x} =
  SQ.elimp X (λ x → hom f x ≡ hom g x) q x
  where
  open ≡.≡-Reasoning
  module f = ≈.Hom f
  module g = ≈.Hom g
  q : (a : ⟨ X ⟩)
    → map X Y f.to f.cong (X ⊢[ a ])
    ≡ map X Y g.to g.cong (X ⊢[ a ])
  q a =
    map X Y f.to f.cong (X ⊢[ a ])
      ≡⟨ map-beta X Y f.to f.cong a ⟩
    Y ⊢[ f.to a ]
      ≡⟨ Y ⊢≈[ p ] ⟩
    Y ⊢[ g.to a ]
      ≡⟨ ≡.sym (map-beta X Y g.to g.cong a) ⟩
    map X Y g.to g.cong (X ⊢[ a ]) ∎

QuotientFunctor : Functor (SetoidCat ℓS ℓ≈) (SetCat (ℓS ⊔ ℓ≈))
QuotientFunctor = record
  { ob = _/≈
  ; hom = hom
  ; id = λ {X} → id {X}
  ; comp = comp
  ; resp = λ {X Y f g} → resp {X} {Y} {f} {g} }
