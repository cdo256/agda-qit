
open import QIT.Prelude
open import QIT.Prop
open import QIT.Container.Base hiding (sup)
open import QIT.Category.Base
open import QIT.Category.Set
import QIT.Set.Base as Set
open Set using (_≡h_) renaming (_∘_ to _∘ₛ_)
open import QIT.Functor.Base

-- Define algebras over setoid endofunctors. An algebra for a functor F
-- is a setoid X equipped with a structure map α : F X → X. This is the
-- foundation for defining initial algebras and recursive data types.
module QIT.Algebra.Base {ℓC} (F : Functor (SetCat ℓC) (SetCat ℓC)) where

-- Define an algebra over a setoid endofunctor.
-- This is just a setoid X paired with a homomorphism:
--    α : F X → X
-- This is used for defining initial algebras.

private
  module F = Functor F

-- An F-algebra consists of a setoid carrier X and a structure map α : F X → X.
-- The structure map gives meaning to the functor's operations on the carrier.
-- For example, if F represents tree operations, α tells us how to build trees.
record Algebra : Set (lsuc ℓC) where
  constructor mkAlg
  field
    -- The carrier setoid
    X : Set ℓC
    -- Structure map: interprets F-structure as elements of X
    α : F.ob X → X


-- Homomorphism between F-algebras: a homomorphism of carriers that
-- commutes with the structure maps. If f : X → Y is an algebra homomorphism,
-- then f(α(fx)) = β(F(f)(fx)) for all fx : F X.
record Hom (Xα Yβ : Algebra) : Set (lsuc ℓC) where
  constructor mkHom
  open Algebra Xα
  open Algebra Yβ renaming (X to Y; α to β)
  field
    -- Underlying homomorphism between carriers
    hom : X → Y
    -- Commutativity condition: the square commutes
    comm : β ∘ₛ F.hom hom ≡h hom ∘ₛ α

-- An initial algebra has a unique homomorphism to every other algebra.
-- This property characterizes recursive data types: the initial algebra
-- gives the "freely generated" elements with no additional equations.
record IsInitial (Xα : Algebra) : Set (lsuc ℓC) where
  constructor mkIsInitial
  open Algebra Xα
  open Hom
  field
    -- Recursor: unique map to any algebra
    rec : ∀ Yβ → Hom Xα Yβ
    -- Uniqueness: any algebra homomorphism equals the recursor
    unique : ∀ Yβ → (f : Hom Xα Yβ) → f .hom ≡h rec Yβ .hom

-- record _≈'_ (Xα Yβ : Algebra) : Set (lsuc ℓC) where
--   constructor mk≈
--   open Algebra Xα
--   open Algebra Yβ renaming (X to Y; α to β)
--   field
--     ob : X ≡ Y
--     struct : ∀ (x : F.ob X) → ≡.subst (λ x → x) ob (α x) ≡ β (≡.subst F.ob ob x)

_≈_ : {Xα Yβ : Algebra} (f g : Hom Xα Yβ) → Prop ℓC
f ≈ g = f.hom ≡h g.hom
  where
  module f = Hom f
  module g = Hom g

id : {Xα : Algebra} → Hom Xα Xα
id {Xα} = mkHom Set.id p
  where
  open Algebra Xα
  p : ∀ {x} → α (F.hom Set.id x) ≡ α x
  p {x} = ≡.cong α F.id

_∘_ : {Xα Yβ Zγ : Algebra} → Hom Yβ Zγ → Hom Xα Yβ → Hom Xα Zγ
_∘_ {Xα} {Yβ} {Zγ} g f = mkHom h p
  where
  open Algebra Xα
  open Algebra Yβ renaming (X to Y; α to β)
  open Algebra Zγ renaming (X to Z; α to γ)
  open module f = Hom f
  open module g = Hom g
  h : X → Z
  h = g.hom Set.∘ f.hom
  p : ∀ {x} → γ (F.hom h x) ≡ h (α x)
  p {x} =
    γ (F.hom (g.hom Set.∘ f.hom) x)
      ≡⟨ ≡.cong γ (F.comp f.hom g.hom) ⟩
    γ (F.hom g.hom (F.hom f.hom x))
      ≡⟨ g.comm ⟩
    g.hom (β (F.hom f.hom x))
      ≡⟨ ≡.cong g.hom f.comm ⟩
    g.hom (f.hom (α x)) ∎
    where open ≡.≡-Reasoning

∘-resp-≈ : {Xα Yβ Zγ : Algebra} {f h : Hom Yβ Zγ} {g i : Hom Xα Yβ}
         → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} p q = r
  where
  open Hom
  r : f .hom ∘ₛ g .hom ≡h h .hom ∘ₛ i .hom
  r = ≡.trans p (≡.cong (h .hom) q)

AlgebraCategory : Category (lsuc ℓC) (lsuc ℓC) ℓC
AlgebraCategory = record
  { Obj = Algebra
  ; _⇒_ = Hom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = ≡.refl
  ; sym-assoc = ≡.refl
  ; identityˡ = ≡.refl
  ; identityʳ = ≡.refl
  ; identity² = ≡.refl
  ; equiv = record { refl = ≡.refl ; sym = λ p → ≡.sym p ; trans = λ p q → ≡.trans p q }
  ; ∘-resp-≈ = λ {f = f} {h} {g} {i} → ∘-resp-≈ {f = f} {h} {g} {i} 
  }
