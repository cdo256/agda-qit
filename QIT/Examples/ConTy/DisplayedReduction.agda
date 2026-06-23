{-# OPTIONS --allow-unsolved-metas #-}

open import QIT.Prelude
open import QIT.Prop
open import QIT.Prop.HetPath as ≣ using (_≣_)
open import QIT.Relation.Subset
open import QIT.Relation.Base
open import QIT.Relation.Nullary
open import QIT.Examples.ConTy.Erased

module QIT.Examples.ConTy.DisplayedReduction ⦃ a!c* : A!C ⦄ (D : DisplayedAlgebra) (rec : ∀ A → ∃!Rec A) where

module D = DisplayedAlgebra D
A : Algebra
A = TotalAlgebra D
module A = Algebra A
B : Algebra
B = BaseAlgebra
module B = Algebra B
r : Rec A
r = proj₁ (rec A)
module r = Rec r

h : AlgebraHom A B
h = record
  { conʰ = proj₁
  ; tyʰ = proj₁
  ; ∙ʰ = ≡.refl
  ; ▷ʰ = ≡.refl
  ; ιʰ = ≡.refl
  ; πʰ = ≡.refl }
module h = AlgebraHom h

h∘r : Rec B
h∘r = AlgebraComp r h
module h∘r = Rec h∘r

module id = Rec idRec

h∘r≡id : Rec≡ B h∘r idRec
h∘r≡id = transRec≡ (symRec≡ (proj₂ (rec B) h∘r)) (proj₂ (rec B) idRec)

Σ-proj₁-≣ : ∀ {A : Set} {B : A → Set} {x y : Σ A B} 
          → x ≣ y → proj₁ x ≣ proj₁ y
Σ-proj₁-≣ ≣.refl = ≣.refl

Σ-proj₂-≣ : ∀ {A : Set} {B : A → Set} {x y : Σ A B} 
          → x ≣ y → proj₂ x ≣ proj₂ y
Σ-proj₂-≣ ≣.refl = ≣.refl

-- This is the "fiber" version of ≣-to-subst-≡
≣-to-subst-fiber : {Γ Γ' : Con} (p : Γ ≡ Γ') 
                  {Γᴰ : D.Conᴰ Γ} {Γᴰ' : D.Conᴰ Γ'} (q : Γᴰ ≣ Γᴰ')
                  {A : Ty Γ} {A' : Ty Γ'} (r : A ≣ A')
                  {u : D.Tyᴰ Γᴰ A} {v : D.Tyᴰ Γᴰ' A'}
                  → u ≣ v → ≡.subst (λ (γ , α) → D.Tyᴰ γ α)
                  (≡.cong₂ _,_ p {!≣.≣-to-≡ r!}) u ≡ v
≣-to-subst-fiber ≡.refl ≣.refl ≣.refl ≣.refl = ≡.refl

Σ-lift : {A : Set} {B : A → Set} {x y : A} {u : B x} {v : B y}
      → (p : x ≡ y) → subst B p u ≡ v → (x , u) ≡ (y , v)
Σ-lift ≡.refl ≡.refl = ≡.refl

transport-fiber : {Γ Γ' : Con} (pΓ : Γ' ≡ Γ)
                → {A : Ty Γ} {A' : Ty Γ'} (pA : A' ≣ A)
                → {Γᴰ : D.Conᴰ Γ'} (u : D.Tyᴰ Γᴰ A')
                → D.Tyᴰ (subst D.Conᴰ pΓ Γᴰ) A
transport-fiber pΓ pA u = ≡.subst₂ D.Tyᴰ {!!} {!!} {!u!}

r̂ : Elim D
r̂ = record
  { conᴱ = c 
  ; tyᴱ = t
  ; ∙ᴱ = {!!}
  ; ▷ᴱ = {!!}
  ; ιᴱ = {!!}
  ; πᴱ = {!!} }
  where
  open ≡.≡-Reasoning
  open Rec≡ h∘r≡id
  p : ∀ Γ → h∘r.conᴿ Γ ≣ Γ
  p Γ = ≣.≡-to-≣ (con≡ Γ)
  q : ∀ {Γ} A → h∘r.tyᴿ {Γ} A ≣ A
  q {Γ} A = ty≣ Γ A

  c : (Γ : Con) → D.Conᴰ Γ
  c Γ = subst D.Conᴰ (con≡ Γ) (proj₂ (r.conᴿ Γ))

  t : {Γ : Con} (A : Ty Γ) → D.Tyᴰ (c Γ) A
  t {Γ} A = transport-fiber (con≡ Γ) (ty≣ Γ A) (proj₂ (r.tyᴿ A))
  p' : proj₂ (r.conᴿ ∙) ≡ subst D.Conᴰ (≡.sym (con≡ ∙)) D.∙ᴰ
  --- Unification error
  -- p' with r.∙ᴿ
  -- ... | ≡.refl =
  --   proj₂ (r.conᴿ ∙)
  --     ≡⟨ {!!} ⟩
  --   subst D.Conᴰ (≡.sym (con≡ ∙)) D.∙ᴰ ∎

  ∙ᴱ : c ∙ ≡ D.∙ᴰ
  ∙ᴱ =
    c ∙
      ≡⟨ ≡.refl ⟩
    subst D.Conᴰ (con≡ ∙) (proj₂ (r.conᴿ ∙))
      ≡⟨ ≡.cong (subst D.Conᴰ (con≡ ∙)) (p') ⟩
    subst D.Conᴰ (con≡ ∙) (subst D.Conᴰ (≡.sym (con≡ ∙)) D.∙ᴰ)
      ≡⟨ {!≡.subst-subst-sym (con≡ ∙)!} ⟩
    D.∙ᴰ ∎
