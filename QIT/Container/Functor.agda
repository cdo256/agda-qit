open import QIT.Prelude
open import QIT.Setoid
open import QIT.Relation.Binary

open import QIT.Container.Base

module QIT.Container.Functor {ℓS ℓP} (S : Set ℓS) (P : S → Set ℓP) (ℓA ℓA' : Level) where

module F-Ob (A : Setoid ℓA ℓA') where
  open ≈.Setoid A
  record _≈ꟳ'_ (x y : ⟦ S ◁ P ⟧ ⟨ A ⟩) : Set (ℓS ⊔ ℓP ⊔ ℓA') where
    constructor mk≈ꟳ'
    field
      fst≡ : x .proj₁ ≡ y .proj₁
      snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (≡.subst P fst≡ p)

  _≈ꟳ_ = Trunc₂ _≈ꟳ'_
  pattern mk≈ꟳ fst≡ snd≈ = ∣ mk≈ꟳ' fst≡ snd≈ ∣

  flatten≈ꟳ : ∀ s f g → (s , f) ≈ꟳ (s , g) → ∀ p → f p ≈ g p
  flatten≈ꟳ s f g (mk≈ꟳ ≡.refl snd≈) = snd≈

  ≈frefl : Reflexive _≈ꟳ_
  ≈frefl = mk≈ꟳ ≡.refl (λ p → refl)

  ≈fsym : Symmetric _≈ꟳ_
  ≈fsym {x} {y} (mk≈ꟳ fst≡ snd≈) =
    mk≈ꟳ (≡.sym fst≡) λ p → sym (snd≈⁻¹ p)
    where
    u : ∀ p → x .proj₂ (subst P (≡.sym fst≡) p) ≈
              y .proj₂ (subst P fst≡
                        (subst P (≡.sym fst≡) p))
    u p = snd≈ (subst P (≡.sym fst≡) p)
    v : ∀ p → (subst P fst≡ (subst P (≡.sym fst≡) p))
            ≡ p
    v p = ≡.subst-subst-sym fst≡
    snd≈⁻¹ : ∀ p → x .proj₂ (subst P (≡.sym fst≡) p) ≈ y .proj₂ p
    snd≈⁻¹ p =
      substp (λ ○ → x .proj₂ (subst P (≡.sym fst≡) p) ≈ y .proj₂ ○)
              (v p) (snd≈ (subst P (≡.sym fst≡) p))

  ≈ftrans : Transitive _≈ꟳ_
  ≈ftrans {x = x} {y} {z} (mk≈ꟳ fst≡1 snd≈1) (mk≈ꟳ fst≡2 snd≈2) =
    mk≈ꟳ (≡.trans fst≡1 fst≡2) v
    where
    u : ∀ p → x .proj₂ p ≈ z .proj₂ (subst P fst≡2 (subst P fst≡1 p))
    u p = trans (snd≈1 p) (snd≈2 (subst P fst≡1 p))
    v : ∀ p → x .proj₂ p ≈ z .proj₂ (subst P (≡.trans fst≡1 fst≡2) p)
    v p = substp (λ ○ → x .proj₂ p ≈ z .proj₂ ○) (≡.subst-subst fst≡1) (u p)

  F-ob : Setoid (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
  F-ob = record
    { Carrier = ⟦ S ◁ P ⟧ ⟨ A ⟩
    ; _≈_ = _≈ꟳ_
    ; isEquivalence = record
      { refl = ≈frefl
      ; sym = ≈fsym
      ; trans = ≈ftrans } }

open F-Ob using (F-ob) public

module F-Mor {A B : Setoid ℓA ℓA'} (f : ≈.Hom A B) where
  module A = ≈.Setoid A
  module B = ≈.Setoid B
  module f = ≈.Hom f
  open F-Ob
  ⟦_⟧h : ⟦ S ◁ P ⟧ ⟨ A ⟩ → ⟦ S ◁ P ⟧ ⟨ B ⟩
  ⟦ s , g ⟧h = s , λ x → f.to (g x)
  congh : ∀ {x y} → (F-ob A Setoid.≈ x) y → (B ≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
  congh (mk≈ꟳ fst≡ snd≈) = mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))
  F-mor : ≈.Hom (F-ob A) (F-ob B)
  F-mor = record
    { to = ⟦_⟧h
    ; cong = congh
    }

open F-Mor using (F-mor) public

F-id : {S : Setoid ℓA ℓA'} → F-mor {A = S} ≈.idHom ≈h ≈.idHom
F-id {S} {s , f} = F-Ob.mk≈ꟳ ≡.refl λ p → S.refl {f p}
  where
  module S = ≈.Setoid S


module F-Comp {S T U : Setoid ℓA ℓA'} (f : ≈.Hom S T) (g : ≈.Hom T U) where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module U = ≈.Setoid U
  module f = ≈.Hom f
  module g = ≈.Hom g
  open F-Ob

  F-comp : F-mor (g ≈.∘ f) ≈h (F-mor g ≈.∘ F-mor f)
  F-comp =
    mk≈ꟳ ≡.refl λ p → (≈.Hom.cong g) (≈.Hom.cong f f.S.refl)

open F-Comp using (F-comp) public

module F-Resp
  {S T : Setoid ℓA ℓA'}
  (f g : ≈.Hom S T)
  (f≈g : f ≈h g)
  where
  module S = ≈.Setoid S
  module T = ≈.Setoid T
  module f = ≈.Hom f
  module g = ≈.Hom g
  open F-Ob
  open F-Mor hiding (F-mor)

  F-resp : F-mor f ≈h F-mor g
  F-resp = mk≈ꟳ ≡.refl λ _ → f≈g

open F-Resp using (F-resp) public

F : ≈.Functor ℓA ℓA' (ℓS ⊔ ℓP ⊔ ℓA) (ℓS ⊔ ℓP ⊔ ℓA')
F = record
  { F-ob = F-ob
  ; F-mor = F-mor
  ; F-id = F-id
  ; F-comp = F-comp
  ; F-resp = F-resp }

