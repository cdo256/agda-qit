module QIT.Examples.ConTy.Tagged where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
open import QIT.Relation.Binary
open import QIT.Category.Base

record Algebra : Set₁ where
  field
    CT : Set
    [_] : CT → CT
    k̂ : CT
    kk̂ : [ k̂ ] ≡ k̂
    ĉ : CT
    kĉ : [ ĉ ] ≡ k̂
    t̂ : (γ : CT) (kγ : [ γ ] ≡ ĉ) → CT
    kt̂ : (γ : CT) (kγ : [ γ ] ≡ ĉ) → [ t̂ γ kγ ] ≡ k̂

    ∙ : CT
    k∙ : [ ∙ ] ≡ ĉ
    ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ) → CT
    k▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → [ ▷ γ kγ a ka ] ≡ ĉ
    u : (γ : CT) (kγ : [ γ ] ≡ ĉ) → CT
    ku : (γ : CT) (kγ : [ γ ] ≡ ĉ) → [ u γ kγ ] ≡ t̂ γ kγ 
    π : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (ka : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → CT
    kπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → [ π γ kγ a ka b kb ] ≡ t̂ γ kγ
    σ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (ka : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → CT
    kσ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → [ σ γ kγ a ka b kb ] ≡ t̂ γ kγ
    σ▷ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → (▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb)
      ≡ ▷ γ kγ (σ γ kγ a ka b kb) (kσ γ kγ a ka b kb)
    σπ : (γ : CT) (kγ : [ γ ] ≡ ĉ)
      → (a : CT) (ka : [ a ] ≡ t̂ γ kγ)
      → (b : CT) (kb : [ b ] ≡ t̂ (▷ γ kγ a ka) (k▷ γ kγ a ka))
      → (c : CT) (kc : [ c ] ≡ t̂ (▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb)
                                 (k▷ (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb))
      → π γ kγ a ka (π (▷ γ kγ a ka) (k▷ γ kγ a ka) b kb c kc)
                    (kπ (▷ γ _ a _) (k▷ γ kγ a ka) b kb c kc)
      ≡ π γ kγ (σ γ kγ a ka b kb) (kσ γ kγ a ka b kb) c
        (≡.trans kc (≡.dcongsp t̂ (σ▷ γ kγ a ka b kb)))

-- A morphism of Tagged algebras is a function on the single sort CT
-- that preserves all the operations.  Because _≡_ is Prop-valued in
-- this development, every proof argument is proof-irrelevant: any two
-- inhabitants of x ≡ y are definitionally equal.  This means
--
--   • for id  : every field is refl (all proof arguments collapse)
--   • for _∘_ : the "lifted" proof positions can be left as _ and
--               Agda solves them from the Prop constraint
record Hom (A B : Algebra) : Set₁ where
  private
    module A = Algebra A
    module B = Algebra B
  field
    ct  : A.CT → B.CT

    -- [_] is natural
    []ʰ : ∀ x → ct (A.[ x ]) ≡ B.[ ct x ]

    -- kinds
    k̂ʰ  : ct A.k̂ ≡ B.k̂
    ĉʰ  : ct A.ĉ ≡ B.ĉ

    -- type-kind constructor
    -- The lifted proof  trans (sym ([]ʰ γ)) (trans (cong ct kγ) ĉʰ)
    -- has the right type  B.[ ct γ ] ≡ B.ĉ ;
    -- since that is a Prop it is definitionally the unique such proof.
    t̂ʰ  : ∀ γ (kγ : A.[ γ ] ≡ A.ĉ)
         → ct (A.t̂ γ kγ)
         ≡ B.t̂ (ct γ) (≡.trans (≡.sym ([]ʰ γ)) (≡.trans (≡.cong ct kγ) ĉʰ))

    -- empty context
    ∙ʰ  : ct A.∙ ≡ B.∙

    -- context extension
    ▷ʰ  : ∀ γ (kγ : A.[ γ ] ≡ A.ĉ)
            a (ka : A.[ a ] ≡ A.t̂ γ kγ)
         → ct (A.▷ γ kγ a ka)
         ≡ B.▷ (ct γ) (≡.trans (≡.sym ([]ʰ γ)) (≡.trans (≡.cong ct kγ) ĉʰ))
               (ct a) (≡.trans (≡.sym ([]ʰ a)) (≡.trans (≡.cong ct ka) (t̂ʰ γ kγ)))

    -- ι-type  (called u in Tagged)
    uʰ  : ∀ γ (kγ : A.[ γ ] ≡ A.ĉ)
         → ct (A.u γ kγ)
         ≡ B.u (ct γ) (≡.trans (≡.sym ([]ʰ γ)) (≡.trans (≡.cong ct kγ) ĉʰ))

    πʰ  : ∀ γ (kγ : A.[ γ ] ≡ A.ĉ)
            a (ka : A.[ a ] ≡ A.t̂ γ kγ)
            b (kb : A.[ b ] ≡ A.t̂ (A.▷ γ kγ a ka) (A.k▷ γ kγ a ka))
         → ct (A.π γ kγ a ka b kb)
         ≡ B.π (ct γ) (≡.trans (≡.sym ([]ʰ γ)) (≡.trans (≡.cong ct kγ) ĉʰ))
               (ct a)  (≡.trans (≡.sym ([]ʰ a)) (≡.trans (≡.cong ct ka) (t̂ʰ γ kγ)))
               (ct b)  (≡.trans
                          (≡.trans (≡.sym ([]ʰ b))
                                   (≡.trans (≡.cong ct kb)
                                            (t̂ʰ (A.▷ γ kγ a ka) (A.k▷ γ kγ a ka))))
                          (≡.dcongsp B.t̂ (▷ʰ γ kγ a ka)))

    -- Σ-type
    σʰ  : ∀ γ (kγ : A.[ γ ] ≡ A.ĉ)
            a (ka : A.[ a ] ≡ A.t̂ γ kγ)
            b (kb : A.[ b ] ≡ A.t̂ (A.▷ γ kγ a ka) (A.k▷ γ kγ a ka))
         → ct (A.σ γ kγ a ka b kb)
         ≡ B.σ (ct γ) (≡.trans (≡.sym ([]ʰ γ)) (≡.trans (≡.cong ct kγ) ĉʰ))
               (ct a)  (≡.trans (≡.sym ([]ʰ a)) (≡.trans (≡.cong ct ka) (t̂ʰ γ kγ)))
               (ct b)  (≡.trans
                          (≡.trans (≡.sym ([]ʰ b))
                                   (≡.trans (≡.cong ct kb)
                                            (t̂ʰ (A.▷ γ kγ a ka) (A.k▷ γ kγ a ka))))
                          (≡.dcongsp B.t̂ (▷ʰ γ kγ a ka)))

open Hom public

-- Identity morphism.
-- Every field is refl: Prop-irrelevance makes all computed proofs
-- collapse to the original proof arguments definitionally.
id : ∀ {A} → Hom A A
id = record
  { ct  = λ x → x
  ; []ʰ = λ _ → ≡.refl
  ; k̂ʰ  = ≡.refl
  ; ĉʰ  = ≡.refl
  ; t̂ʰ  = λ _ _ → ≡.refl
  ; ∙ʰ  = ≡.refl
  ; ▷ʰ  = λ _ _ _ _ → ≡.refl
  ; uʰ  = λ _ _ → ≡.refl
  ; πʰ  = λ _ _ _ _ _ _ → ≡.refl
  ; σʰ  = λ _ _ _ _ _ _ → ≡.refl
  }

-- Composition.
-- For each field we apply cong g.ct to f's proof, then g's proof.
-- The "lifted" proof arguments passed to g's fields are left as _:
-- they are Prop-valued so Agda can always solve them.
_∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
_∘_ g f = record
  { ct  = λ x → g.ct (f.ct x)
  ; []ʰ = λ x  → ≡.trans (≡.cong g.ct (f.[]ʰ x)) (g.[]ʰ (f.ct x))
  ; k̂ʰ  = ≡.trans (≡.cong g.ct f.k̂ʰ) g.k̂ʰ
  ; ĉʰ  = ≡.trans (≡.cong g.ct f.ĉʰ) g.ĉʰ
  ; t̂ʰ  = λ γ kγ →
      ≡.trans (≡.cong g.ct (f.t̂ʰ γ kγ))
              (g.t̂ʰ (f.ct γ) _)
  ; ∙ʰ  = ≡.trans (≡.cong g.ct f.∙ʰ) g.∙ʰ
  ; ▷ʰ  = λ γ kγ a ka →
      ≡.trans (≡.cong g.ct (f.▷ʰ γ kγ a ka))
              (g.▷ʰ (f.ct γ) _ (f.ct a) _)
  ; uʰ  = λ γ kγ →
      ≡.trans (≡.cong g.ct (f.uʰ γ kγ))
              (g.uʰ (f.ct γ) _)
  ; πʰ  = λ γ kγ a ka b kb →
      ≡.trans (≡.cong g.ct (f.πʰ γ kγ a ka b kb))
              (g.πʰ (f.ct γ) _ (f.ct a) _ (f.ct b) _)
  ; σʰ  = λ γ kγ a ka b kb →
      ≡.trans (≡.cong g.ct (f.σʰ γ kγ a ka b kb))
              (g.σʰ (f.ct γ) _ (f.ct a) _ (f.ct b) _)
  }
  where
  module f = Hom f
  module g = Hom g

-- Morphism equality: pointwise on CT.
-- Because every proof field is in Prop, equality of morphisms
-- reduces to equality of the underlying CT-function.
record _≈_ {A B : Algebra} (f g : Hom A B) : Prop ℓ0 where
  constructor mk≈
  field
    ct≡ : ∀ x → f .ct x ≡ g .ct x

open _≈_ public

isEquiv≈ : ∀ {A B : Algebra} → IsEquivalence (_≈_ {A} {B})
isEquiv≈ = record
  { refl  = mk≈ λ _ → ≡.refl
  ; sym   = λ (mk≈ p) → mk≈ λ x → ≡.sym (p x)
  ; trans = λ (mk≈ p) (mk≈ q) → mk≈ λ x → ≡.trans (p x) (q x)
  }

∘-resp-≈ : ∀ {A B C : Algebra} {f h : Hom B C} {g i : Hom A B}
          → f ≈ h → g ≈ i → (f ∘ g) ≈ (h ∘ i)
∘-resp-≈ {f = f} {h} {g} {i} (mk≈ p) (mk≈ q) =
  mk≈ λ x → ≡.trans (≡.cong (f .ct) (q x)) (p (i .ct x))
      

Cat : Category (lsuc ℓ0) (lsuc ℓ0) ℓ0
Cat = record
  { Obj       = Algebra
  ; _⇒_       = Hom
  ; _≈_      = _≈_
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = mk≈ λ _ → ≡.refl
  ; sym-assoc = mk≈ λ _ → ≡.refl
  ; identityˡ = mk≈ λ _ → ≡.refl
  ; identityʳ = mk≈ λ _ → ≡.refl
  ; identity² = mk≈ λ _ → ≡.refl
  ; equiv     = isEquiv≈
  ; ∘-resp-≈  = ∘-resp-≈
  }
