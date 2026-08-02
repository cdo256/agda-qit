open import QIT.Prelude

module QIT.Examples.ConTy.WeaklyTagged
  ⦃ pathElim* : PathElim ⦄
  where

open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
open import QIT.Relation.Binary using (IsEquivalence)
open import QIT.Category.Base

infix  4 _≈_
infixr 9 _∘_

record Algebra ℓX : Set (lsuc ℓX) where
  no-eta-equality
  field
    CT : Set ℓX
    [_] : CT → CT
    k̂ : CT
    ĉ : CT
    t̂ : (γ : CT) → CT

    ∙ : CT
    k∙ : [ ∙ ] ≡ ĉ
    ▷ : (γ : CT) (a : CT) → CT
    k▷ : (γ : CT) (a : CT)
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ ▷ γ a ] ≡ ĉ
    ▷-γ : ∀ γ a
      → [ ▷ γ a ] ≡ ĉ
      → [ γ ] ≡ ĉ
    ▷-a : ∀ γ a
      → [ ▷ γ a ] ≡ ĉ
      → [ a ] ≡ t̂ γ
    u : (γ : CT) → CT
    ku : (γ : CT)
      → [ γ ] ≡ ĉ
      → [ u γ ] ≡ t̂ γ 
    u-γ : ∀ γ
      → [ u γ ] ≡ t̂ γ
      → [ γ ] ≡ ĉ
    π : (γ : CT) (a : CT) (b : CT) → CT
    kπ : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ π γ a b ] ≡ t̂ γ 
    π-γ : (γ : CT) (a : CT) (b : CT) 
      → [ π γ a b ] ≡ t̂ γ 
      → [ γ ] ≡ ĉ
    π-a : (γ : CT) (a : CT) (b : CT) 
      → [ π γ a b ] ≡ t̂ γ 
      → [ a ] ≡ t̂ γ
    π-b : (γ : CT) (a : CT) (b : CT) 
      → [ π γ a b ] ≡ t̂ γ 
      → [ b ] ≡ t̂ (▷ γ a)
    σ : (γ : CT) (a : CT) (b : CT) → CT
    kσ : (γ : CT) (a : CT) (b : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ σ γ a b ] ≡ t̂ γ 
    σ-γ : (γ : CT) (a : CT) (b : CT) 
      → [ σ γ a b ] ≡ t̂ γ 
      → [ γ ] ≡ ĉ
    σ-a : (γ : CT) (a : CT) (b : CT) 
      → [ σ γ a b ] ≡ t̂ γ 
      → [ a ] ≡ t̂ γ
    σ-b : (γ : CT) (a : CT) (b : CT) 
      → [ σ γ a b ] ≡ t̂ γ 
      → [ b ] ≡ t̂ (▷ γ a)
    σ▷ : (γ : CT) (a : CT) (b : CT)
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → ▷ (▷ γ a) b
      ≡ ▷ γ (σ γ a b)
    σπ : (γ : CT)
      → (a : CT) 
      → (b : CT) 
      → (c : CT) 
      → [ γ ] ≡ ĉ
      → [ a ] ≡ t̂ γ
      → [ b ] ≡ t̂ (▷ γ a)
      → [ c ] ≡ t̂ (▷ (▷ γ a) b)
      → π γ a (π (▷ γ a) b c)
      ≡ π γ (σ γ a b) c

record AlgebraWithMotive {ℓA} (M : Set ℓA) : Set (lsuc ℓA) where
  field
    DA : Algebra ℓA
  open Algebra DA public
  field
    motive : CT ≡ M

record Hom (A : Algebra ℓA) (B : Algebra ℓB) : Set (ℓA ⊔ ℓB) where
  no-eta-equality
  private
    module A = Algebra A
    module B = Algebra B
  field
    θ : A.CT → B.CT
    [_] : ∀ (x : A.CT) → θ (A.[ x ]) ≡ B.[ θ x ]
    k̂ : θ A.k̂ ≡ B.k̂
    ĉ : θ A.ĉ ≡ B.ĉ
    t̂ : ∀ (γ : A.CT) → θ (A.t̂ γ) ≡ B.t̂ (θ γ)
    ∙ : θ A.∙ ≡ B.∙
    ▷ : ∀ (γ : A.CT) (a : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → A.[ a ] ≡ A.t̂ γ
      → θ (A.▷ γ a) ≡ B.▷ (θ γ) (θ a)
    u : ∀ (γ : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → θ (A.u γ) ≡ B.u (θ γ)
    π : ∀ (γ : A.CT) (a : A.CT) (b : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → A.[ a ] ≡ A.t̂ γ
      → A.[ b ] ≡ A.t̂ (A.▷ γ a)
      → θ (A.π γ a b) ≡ B.π (θ γ) (θ a) (θ b)
    σ : ∀ (γ : A.CT) (a : A.CT) (b : A.CT)
      → A.[ γ ] ≡ A.ĉ
      → A.[ a ] ≡ A.t̂ γ
      → A.[ b ] ≡ A.t̂ (A.▷ γ a)
      → θ (A.σ γ a b) ≡ B.σ (θ γ) (θ a) (θ b)

id : ∀ {ℓA} {A : Algebra ℓA} → Hom A A
id = record
  { θ = λ x → x
  ; [_] = λ _ → ≡.refl
  ; k̂ = ≡.refl
  ; ĉ = ≡.refl
  ; t̂ = λ _ → ≡.refl
  ; ∙ = ≡.refl
  ; ▷ = λ _ _ _ _ → ≡.refl
  ; u = λ _ _ → ≡.refl
  ; π = λ _ _ _ _ _ _ → ≡.refl
  ; σ = λ _ _ _ _ _ _ → ≡.refl
  }

_∘_ : ∀ {ℓA ℓB ℓC} {A : Algebra ℓA} {B : Algebra ℓB} {C : Algebra ℓC} → Hom B C → Hom A B → Hom A C
_∘_ {A = A} {B} {C} g f = record
  { θ = λ x → g.θ (f.θ x)
  ; [_] = λ x → ≡.trans (≡.cong g.θ (f.[_] x)) (g.[_] (f.θ x))
  ; k̂ = ≡.trans (≡.cong g.θ f.k̂) g.k̂
  ; ĉ = ≡.trans (≡.cong g.θ f.ĉ) g.ĉ
  ; t̂ = λ x → ≡.trans (≡.cong g.θ (f.t̂ x)) (g.t̂ (f.θ x))
  ; ∙ = ≡.trans (≡.cong g.θ f.∙) g.∙
  ; ▷ = λ x a kx ka → ≡.trans (≡.cong g.θ (f.▷ x a kx ka)) (g.▷ (f.θ x) (f.θ a) (kx' x kx) (ka' x a ka))
  ; u = λ x kx → ≡.trans (≡.cong g.θ (f.u x kx)) (g.u (f.θ x) (kx' x kx))
  ; π = λ x a b kx ka kb → ≡.trans (≡.cong g.θ (f.π x a b kx ka kb)) (g.π (f.θ x) (f.θ a) (f.θ b) (kx' x kx) (ka' x a ka) (kb' x a b kx ka kb))
  ; σ = λ x a b kx ka kb → ≡.trans (≡.cong g.θ (f.σ x a b kx ka kb)) (g.σ (f.θ x) (f.θ a) (f.θ b) (kx' x kx) (ka' x a ka) (kb' x a b kx ka kb))
  }
  where
  module A = Algebra A
  module B = Algebra B
  module C = Algebra C
  module f = Hom f
  module g = Hom g

  kx' : ∀ x → A.[ x ] ≡ A.ĉ → B.[ f.θ x ] ≡ B.ĉ
  kx' x kx = ≡.trans (≡.sym (f.[_] x)) (≡.trans (≡.cong f.θ kx) f.ĉ)

  ka' : ∀ x a → A.[ a ] ≡ A.t̂ x → B.[ f.θ a ] ≡ B.t̂ (f.θ x)
  ka' x a ka = ≡.trans (≡.sym (f.[_] a)) (≡.trans (≡.cong f.θ ka) (f.t̂ x))

  kb' : ∀ x a b
    → A.[ x ] ≡ A.ĉ
    → A.[ a ] ≡ A.t̂ x
    → A.[ b ] ≡ A.t̂ (A.▷ x a)
    → B.[ f.θ b ] ≡ B.t̂ (B.▷ (f.θ x) (f.θ a))
  kb' x a b kx ka kb =
    ≡.trans
      (≡.trans (≡.sym (f.[_] b)) (≡.trans (≡.cong f.θ kb) (f.t̂ (A.▷ x a))))
      (≡.cong B.t̂ (f.▷ x a kx ka))

record _≈_ {ℓA ℓB} {A : Algebra ℓA} {B : Algebra ℓB} (f g : Hom A B) : Prop (ℓA ⊔ ℓB) where
  constructor mk≈
  module f = Hom f
  module g = Hom g
  field
    θ≡ : ∀ x → f.θ x ≡ g.θ x

isEquiv≈ : ∀ {ℓA ℓB} {A : Algebra ℓA} {B : Algebra ℓB} → IsEquivalence (_≈_ {A = A} {B})
isEquiv≈ = record
  { refl = mk≈ λ _ → ≡.refl
  ; sym = λ (mk≈ p) → mk≈ λ x → ≡.sym (p x)
  ; trans = λ (mk≈ p) (mk≈ q) → mk≈ λ x → ≡.trans (p x) (q x)
  }

open import QIT.Setoid

HomSetoid : ∀ {ℓA ℓB} (A : Algebra ℓA) (B : Algebra ℓB) → Setoid (ℓA ⊔ ℓB) (ℓA ⊔ ℓB)
HomSetoid A B = record
  { Carrier = Hom A B
  ; _≈_ = _≈_
  ; isEquivalence = isEquiv≈ }

∘-resp-≈ : ∀ {ℓA ℓB ℓC} {A : Algebra ℓA} {B : Algebra ℓB} {C : Algebra ℓC} {f h : Hom B C} {g i : Hom A B}
  → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} (mk≈ p) (mk≈ q) =
  mk≈ λ x → ≡.trans (≡.cong (f.θ) (q x)) (p (i.θ x))
  where
  module f = Hom f
  module g = Hom g
  module h = Hom h
  module i = Hom i

Cat : ∀ ℓX → Category (lsuc ℓX) ℓX ℓX
Cat ℓX = record
  { Obj = Algebra ℓX
  ; _⇒_ = Hom
  ; _≈_ = _≈_
  ; id = id
  ; _∘_ = _∘_
  ; assoc = mk≈ λ _ → ≡.refl
  ; sym-assoc = mk≈ λ _ → ≡.refl
  ; identityˡ = mk≈ λ _ → ≡.refl
  ; identityʳ = mk≈ λ _ → ≡.refl
  ; identity² = mk≈ λ _ → ≡.refl
  ; equiv = isEquiv≈
  ; ∘-resp-≈ = ∘-resp-≈
  }

LiftAlgebra : ∀ {ℓX} ℓY → Algebra ℓX → Algebra (ℓX ⊔ ℓY)
LiftAlgebra ℓY A = record
  { CT = Lift ℓY A.CT
  ; [_] = λ (lift x) → lift (A.[ x ])
  ; k̂ = lift A.k̂
  ; ĉ = lift A.ĉ
  ; t̂ = λ (lift γ) → lift (A.t̂ γ)
  ; ∙ = lift A.∙
  ; k∙ = ↑ A.k∙
  ; ▷ = λ (lift γ) (lift a) → lift (A.▷ γ a)
  ; k▷ = λ (lift γ) (lift a) kγ ka → ↑ (A.k▷ γ a (↓ kγ) (↓ ka))
  ; ▷-γ = λ (lift γ) (lift a) k▷ → ↑ (A.▷-γ γ a (↓ k▷))
  ; ▷-a = λ (lift γ) (lift a) k▷ → ↑ (A.▷-a γ a (↓ k▷))
  ; u = λ (lift γ) → lift (A.u γ)
  ; ku = λ (lift γ) kγ → ↑ (A.ku γ (↓ kγ))
  ; u-γ = λ (lift γ) ku → ↑ (A.u-γ γ (↓ ku))
  ; π = λ (lift γ) (lift a) (lift b) → lift (A.π γ a b)
  ; kπ = λ (lift γ) (lift a) (lift b) kγ ka kb
       → ↑ (A.kπ γ a b (↓ kγ) (↓ ka) (↓ kb))
  ; π-γ = λ (lift γ) (lift a) (lift b) kπ
       → ↑ (A.π-γ γ a b (↓ kπ))
  ; π-a = λ (lift γ) (lift a) (lift b) kπ
       → ↑ (A.π-a γ a b (↓ kπ))
  ; π-b = λ (lift γ) (lift a) (lift b) kπ
       → ↑ (A.π-b γ a b (↓ kπ))
  ; σ = λ (lift γ) (lift a) (lift b)
      → lift (A.σ γ a b)
  ; kσ = λ (lift γ) (lift a) (lift b) kγ ka kb
       → ↑ (A.kσ γ a b (↓ kγ) (↓ ka) (↓ kb))
  ; σ-γ = λ (lift γ) (lift a) (lift b) kσ
       → ↑ (A.σ-γ γ a b (↓ kσ))
  ; σ-a = λ (lift γ) (lift a) (lift b) kσ
       → ↑ (A.σ-a γ a b (↓ kσ))
  ; σ-b = λ (lift γ) (lift a) (lift b) kσ
       → ↑ (A.σ-b γ a b (↓ kσ))
  ; σ▷ = λ (lift γ) (lift a) (lift b) kγ ka kb
       → ↑ (A.σ▷ γ a b (↓ kγ) (↓ ka) (↓ kb))
  ; σπ = λ (lift γ) (lift a) (lift b) (lift c) kγ ka kb kc
       → ↑ (A.σπ γ a b c (↓ kγ) (↓ ka) (↓ kb) (↓ kc))
  }
  where
  module A = Algebra A
  ↑_ : ∀ {x y : A.CT} (p : x ≡ y)
    → lift {ℓA' = ℓP} x ≡ lift {ℓA' = ℓP} y
  ↑ p = ≡.cong lift p
  ↓_ : ∀ {x y : Lift ℓP A.CT} (p : x ≡ y)
    → lower {ℓA' = ℓP} x ≡ lower {ℓA' = ℓP} y
  ↓ p = ≡.cong lower p

module Cat ℓA where
  open import QIT.Category.Morphism (Cat ℓA) public
  open import QIT.Category.Initial (Cat ℓA) public
