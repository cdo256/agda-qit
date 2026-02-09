open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Binary

open import QIT.Container.Base

-- Define a setoid functor from a container (S ◁ P).
-- This lifts the container interpretation to work with setoids, creating
-- a functor that preserves equivalence relations. The resulting functor
-- maps setoids to setoids and homomorphisms to homomorphisms.
module QIT.Container.Functor {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓA ℓA' : Level) where

-- Object part of the functor: given a setoid A, construct F A.
-- Elements are pairs (s, f) where s : S and f : P s → ⟨A⟩.
-- Equivalence is defined pointwise: (s, f) ≈ (t, g) if s ≡ t and f p ≈ g p'.
module Ob (A : Setoid ℓA ℓA') where
  open ≈.Setoid A

  -- Technical equivalence relation for container elements.
  -- We need fst≡ to be definitional equality to enable substitution in snd≈.
  record _≈ꟳ'_ (x y : ⟦ S ◁ P ⟧ ⟨ A ⟩) : Set (ℓS ⊔ ℓP ⊔ ℓA') where
    constructor mk≈ꟳ'
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst P fst≡ p)

  -- Truncated equivalence relation to ensure it's a proposition.
  -- Pattern synonym makes the truncation transparent for pattern matching.
  _≈ꟳ_ = Trunc₂ _≈ꟳ'_
  pattern mk≈ꟳ fst≡ snd≈ = ∣ mk≈ꟳ' fst≡ snd≈ ∣

  -- Prove equivalence relation laws for ≈ꟳ
  ≈frefl : Reflexive _≈ꟳ_
  ≈frefl = mk≈ꟳ ≡.refl (λ p → refl)

  ≈fsym : Symmetric _≈ꟳ_
  ≈fsym {x} {y} (mk≈ꟳ ≡.refl snd≈) =
    mk≈ꟳ ≡.refl λ p → sym (snd≈ p)

  ≈ftrans : Transitive _≈ꟳ_
  ≈ftrans {x = x} {y} {z} (mk≈ꟳ ≡.refl snd≈1) (mk≈ꟳ ≡.refl snd≈2) =
    mk≈ꟳ ≡.refl v
    where
    u : ∀ p → x .proj₂ p ≈ z .proj₂ p
    u p = trans (snd≈1 p) (snd≈2 p)
    v : ∀ p → x .proj₂ p ≈ z .proj₂ p
    v p = substp (λ ○ → x .proj₂ p ≈ z .proj₂ ○) ≡.refl (u p)

  -- The setoid F A with container elements and pointwise equivalence
  ob : Setoid (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
  ob = record
    { Carrier = ⟦ S ◁ P ⟧ ⟨ A ⟩
    ; _≈_ = _≈ꟳ_
    ; isEquivalence = record
      { refl = ≈frefl
      ; sym = ≈fsym
      ; trans = ≈ftrans } }

open Ob using (ob) public

-- Morphism part of the functor: lift homomorphisms f : A → B to F f : F A → F B.
-- Apply f pointwise to the function part while preserving the shape.
module Hom {A B : Setoid ℓA ℓA'} (f : ≈.Hom A B) where
  module A = ≈.Setoid A
  module B = ≈.Setoid B
  module f = ≈.Hom f
  open Ob

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
id {S} {s , f} = Ob.mk≈ꟳ ≡.refl λ p → S.refl {f p}
  where
  module S = ≈.Setoid S

-- F preserves composition: F(g ∘ f) ≈ F g ∘ F f
module Comp {S T U : Setoid ℓA ℓA'} (f : ≈.Hom S T) (g : ≈.Hom T U) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module U = ≈.Setoid U
  module f = ≈.Hom f
  module g = ≈.Hom g
  open Ob

  comp : hom (g ≈.∘ f) ≈h (hom g ≈.∘ hom f)
  comp =
    mk≈ꟳ ≡.refl λ p → (≈.Hom.cong g) (≈.Hom.cong f f.S.refl)

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
  open Ob
  open Hom hiding (hom)

  resp : hom f ≈h hom g
  resp = mk≈ꟳ ≡.refl λ _ → f≈g

open Resp using (resp) public

-- The complete setoid functor induced by container (S ◁ P)
F : ≈.Functor ℓA ℓA' (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
F = record
  { ob = ob
  ; hom = hom
  ; id = id
  ; comp = comp
  ; resp = resp }
