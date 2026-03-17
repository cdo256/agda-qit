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

  -- Postulates: when pattern matching on refl, subst computes to identity
  -- This is needed because _≡_ lives in Prop, so we can't pattern match in Set-returning functions
  private postulate
    subst-refl-helper : ∀ {s : S} (f : P s → Carrier) (p : P s)
                      → f p ≈ f (≡.subst P ≡.refl p)
    subst-refl-sym-helper : ∀ {s : S} (f : P s → Carrier) (p : P s)
                          → f (≡.subst P ≡.refl p) ≈ f p

  -- Technical equivalence relation for container elements.
  -- We need fst≡ to be definitional equality to enable substitution in snd≈.
  record _≈ꟳ_ (x y : ⟦ S ◁ P ⟧ ⟨ A ⟩) : Prop (ℓS ⊔ ℓP ⊔ ℓA') where
    pattern
    constructor mk≈ꟳ
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst P fst≡ p)


  -- Prove equivalence relation laws for ≈ꟳ
  ≈frefl : Reflexive _≈ꟳ_
  ≈frefl {x} = mk≈ꟳ ≡.refl (λ p → subst-refl-helper (x .proj₂) p)

  ≈fsym : Symmetric _≈ꟳ_
  -- TODO: Properly handle symmetry with Jp eliminator
  -- For now we pattern match on refl which works when it gives definitional equality
  ≈fsym {x} {y} (mk≈ꟳ ≡.refl snd≈) =
    mk≈ꟳ ≡.refl λ p → sym ?

--   ≈ftrans : Transitive _≈ꟳ_
--   -- TODO: Properly handle transitivity with Jp eliminator for nested pattern matches
--   -- For now we postulate this case works when pattern matching gives definitional equality
--   ≈ftrans {x = x} {y} {z} (mk≈ꟳ ≡.refl snd≈1) (mk≈ꟳ ≡.refl snd≈2) =
--     mk≈ꟳ ≡.refl λ p → trans (subst-refl-helper (x .proj₂) p)
--                             (trans (snd≈1 p)
--                                    (trans (snd≈2 (≡.subst P ≡.refl p))
--                                           (sym (subst-refl-helper (x .proj₂) (≡.subst P ≡.refl p)))))

--   -- The setoid F A with container elements and pointwise equivalence
--   ob : Setoid (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
--   ob = record
--     { Carrier = ⟦ S ◁ P ⟧ ⟨ A ⟩
--     ; _≈_ = _≈ꟳ_
--     ; isEquivalence = record
--       { refl = ≈frefl
--       ; sym = ≈fsym
--       ; trans = ≈ftrans } }

-- -- The complete setoid functor induced by container (S ◁ P)
-- F : Functor (SetoidCat ℓA ℓA') (SetoidCat (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA'))
-- F = record
--   { ob = F-Ob.ob
--   ; hom = hom
--   ; id = id
--   ; comp = comp
--   ; resp = λ z → F-Ob.mk≈ꟳ ≡.refl λ _ → z }
--   where
--   -- Morphism part of the functor: lift homomorphisms f : A → B to F f : F A → F B.
--   -- Apply f pointwise to the function part while preserving the shape.
--   module Hom {A B : Setoid ℓA ℓA'} (f : ≈.Hom A B) where
--     module A = ≈.Setoid A
--     module B = ≈.Setoid B
--     module f = ≈.Hom f
--     open F-Ob

--     -- Underlying function: map f over the P s → A part
--     ⟦_⟧h : ⟦ S ◁ P ⟧ ⟨ A ⟩ → ⟦ S ◁ P ⟧ ⟨ B ⟩
--     ⟦ s , g ⟧h = s , λ x → f.to (g x)

--     -- Congruence: F f preserves equivalence
--     congh : ∀ {x y} → (ob A Setoid.≈ x) y → (B ≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
--     congh (mk≈ꟳ fst≡ snd≈) = mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))

--     hom : ≈.Hom (ob A) (ob B)
--     hom = record
--       { to = ⟦_⟧h
--       ; cong = congh
--       }

--   open Hom using (hom) public

--   -- Functorial laws: F preserves identity, composition, and equivalence

--   -- F preserves identity: F(id) ≈ id
--   id : {S : Setoid ℓA ℓA'} → hom {A = S} ≈.idHom ≈h ≈.idHom
--   id {S} {s , f} = F-Ob.mk≈ꟳ ≡.refl λ p → S.refl {f p}
--     where
--     module S = ≈.Setoid S

--   -- F preserves composition: F(g ∘ f) ≈ F g ∘ F f
--   module Comp {S T U : Setoid ℓA ℓA'} (f : ≈.Hom S T) (g : ≈.Hom T U) where
--     module S = ≈.Setoid S
--     module T = ≈.Setoid T
--     module U = ≈.Setoid U
--     module f = ≈.Hom f
--     module g = ≈.Hom g
--     open F-Ob

--     comp : hom (g ≈.∘ f) ≈h (hom g ≈.∘ hom f)
--     comp =
--       mk≈ꟳ ≡.refl λ p → (≈.Hom.cong g) (≈.Hom.cong f f.S.refl)

--   open Comp using (comp) public

--   -- F respects homomorphism equivalence: if f ≈ g then F f ≈ F g
--   module Resp
--     {S T : Setoid ℓA ℓA'}
--     (f g : ≈.Hom S T)
--     (f≈g : f ≈h g)
--     where
--     module S = ≈.Setoid S
--     module T = ≈.Setoid T
--     module f = ≈.Hom f
--     module g = ≈.Hom g
--     open F-Ob
--     open Hom hiding (hom)

--     resp : hom f ≈h hom g
--     resp = mk≈ꟳ ≡.refl λ _ → f≈g

--   open Resp using (resp) public
