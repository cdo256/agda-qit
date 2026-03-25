open import QIT.Prelude
open import QIT.Prop
open import QIT.Setoid
open import QIT.Functor.Base
open import QIT.Category.Setoid
open import QIT.Relation.Binary

open import QIT.Container.Base

-- Define a setoid functor from a container (S ◁ P).
-- This lifts the container interpretation to work with setoids, creating
-- a functor that preserves equivalence relations. The resulting functor
-- maps setoids to setoids and homomorphisms to homomorphisms.
module QIT.Container.Functor {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓA ℓA' : Level) where

module F-Ob (A : Setoid ℓA ℓA') where
  open ≈.Setoid A

  -- Technical equivalence relation for container elements.
  -- We need fst≡ to be definitional equality to enable substitution in snd≈.
  record _≈ꟳ_ (x y : ⟦ S ◁ P ⟧ ⟨ A ⟩) : Prop (ℓS ⊔ ℓP ⊔ ℓA') where
    pattern
    constructor mk≈ꟳ
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst P fst≡ p)

  mk≈ꟳ' : ∀ {s : S} {f g : P s → ⟨ A ⟩}
    → ((i : P s) → f i ≈ g i)
    → (s , f) ≈ꟳ (s , g)
  mk≈ꟳ' {s} {f} {g} f≈g = mk≈ꟳ ≡.refl f≈g

  -- Prove equivalence relation laws for ≈ꟳ
  ≈frefl : Reflexive _≈ꟳ_
  ≈frefl {s , f} = mk≈ꟳ' λ _ → refl

  ≈fsym : Symmetric _≈ꟳ_
  ≈fsym {s , f} {s , g} (mk≈ꟳ ≡.refl f≈g) =
    mk≈ꟳ ≡.refl λ i → sym (f≈g i)

  ≈ftrans : Transitive _≈ꟳ_
  ≈ftrans {s , f} {s , g} {s , h} (mk≈ꟳ ≡.refl f≈g) (mk≈ꟳ ≡.refl g≈h) =
    mk≈ꟳ ≡.refl λ i → trans (f≈g i) (g≈h i)

  -- The setoid F A with container elements and pointwise equivalence
  ob : Setoid (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
  ob = record
    { Carrier = ⟦ S ◁ P ⟧ ⟨ A ⟩
    ; _≈_ = _≈ꟳ_
    ; isEquivalence = record
      { refl = ≈frefl
      ; sym = ≈fsym
      ; trans = ≈ftrans } }

-- The complete setoid functor induced by container (S ◁ P)
F : Functor (SetoidCat ℓA ℓA') (SetoidCat (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA'))
F = record
  { ob = F-Ob.ob
  ; hom = hom
  ; id = id
  ; comp = comp
  ; resp = λ {y = Y} z → F-Ob.mk≈ꟳ' Y λ _ → z }
  where
  -- Morphism part of the functor: lift homomorphisms f : A → B to F f : F A → F B.
  -- Apply f pointwise to the function part while preserving the shape.
  module Hom {A B : Setoid ℓA ℓA'} (f : ≈.Hom A B) where
    module A = ≈.Setoid A
    module B = ≈.Setoid B
    module f = ≈.Hom f
    open F-Ob

    -- Underlying function: map f over the P s → A part
    ⟦_⟧h : ⟦ S ◁ P ⟧ ⟨ A ⟩ → ⟦ S ◁ P ⟧ ⟨ B ⟩
    ⟦ s , g ⟧h = s , λ x → f.to (g x)

    -- Congruence: F f preserves equivalence
    congh : ∀ {x y} → (ob A Setoid.≈ x) y → (B ≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
    congh (mk≈ꟳ fst≡ snd≈) = mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))

    hom : ≈.Hom (ob A) (ob B)
    hom = record
      { to = ⟦_⟧h
      ; cong = congh
      }

  open Hom using (hom) public

  -- Functorial laws: F preserves identity, composition, and equivalence

  -- F preserves identity: F(id) ≈ id
  id : {S : Setoid ℓA ℓA'} → hom {A = S} ≈.idHom ≈h ≈.idHom
  id {S} {s , f} = F-Ob.mk≈ꟳ' S λ _ → S.refl
    where
    module S = ≈.Setoid S

  -- F preserves composition: F(g ∘ f) ≈ F g ∘ F f
  module Comp {S T U : Setoid ℓA ℓA'} (f : ≈.Hom S T) (g : ≈.Hom T U) where
    module S = ≈.Setoid S
    module T = ≈.Setoid T
    module U = ≈.Setoid U
    module f = ≈.Hom f
    module g = ≈.Hom g
    open F-Ob

    comp : hom (g ≈.∘ f) ≈h (hom g ≈.∘ hom f)
    comp =
      mk≈ꟳ' U λ i → (≈.Hom.cong g) (≈.Hom.cong f f.S.refl)

  open Comp using (comp) public

  -- F respects homomorphism equivalence: if f ≈ g then F f ≈ F g
  module Resp
    {S T : Setoid ℓA ℓA'}
    (f g : ≈.Hom S T)
    (f≈g : f ≈h g)
    where
    module S = ≈.Setoid S
    module T = ≈.Setoid T
    module f = ≈.Hom f
    module g = ≈.Hom g
    open F-Ob
    open Hom hiding (hom)

    resp : hom f ≈h hom g
    resp = mk≈ꟳ' T λ _ → f≈g

  open Resp using (resp) public
