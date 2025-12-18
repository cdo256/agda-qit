{-# OPTIONS --type-in-type #-}
module Mobile where

open import Prelude
open import Data.Product
-- open import Function.Bundles
open import Function.Definitions
open import Relation.Binary.PropositionalEquality as ≡
open import Axiom
open import Setoid as ≈
open import Function.Properties.Inverse 
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity)
-- open import Relation.Binary.Structures

private
  l0 : Level
  l0 = lzero

module Mobile (B : Set) where
  open Box
  
  data NodeType : Set where
    l : NodeType
    n : NodeType

  open import Data.Unit
  open import Data.Sum

  Branch : Container l0 l0 
  Branch .Shape = NodeType
  Branch .Position l = Lift l0 ⊥
  Branch .Position n = B

  BTree = W Branch
  
  pattern leaf {f} = sup (l , f)
  pattern node f = sup (n , f)

  Bˢ : Setoid l0 l0
  Bˢ = ≡setoid B
  data _≈ᵗ_ : BTree → BTree → Prop l0 where
    ≈leaf : ∀ {f g} → leaf {f} ≈ᵗ leaf {g}
    ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
          → node f ≈ᵗ node g
    ≈perm : ∀ {f} → (π : SetoidIso Bˢ Bˢ)
          → node f ≈ᵗ node λ b → f (π .SetoidIso.⟦_⟧ b)
    ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u

  ≈refl : ∀ {t} → t ≈ᵗ t
  ≈refl {leaf} = ≈leaf
  ≈refl {node f} = ≈node λ b → ≈refl {f b}

  ≈sym : ∀ {s t} → s ≈ᵗ t → t ≈ᵗ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
  ≈sym (≈perm {f} π) =
    substp' A p x
    where
    module π = SetoidIso π
    π' = SetoidIsoFlip π
    A : (B → B) → Prop l0
    A = λ h → node (λ b → f π.⟦ b ⟧) ≈ᵗ node λ b → f (h b)
    p : (λ b → π.⟦ π.⟦ b ⟧⁻¹ ⟧) ≡p (λ b → b)
    p = funExtp λ b → (π.linv b)
    x : node (λ b → f π.⟦ b ⟧) ≈ᵗ node (λ b → f π.⟦ π.⟦ b ⟧⁻¹ ⟧)
    x = ≈perm {f = λ b → f π.⟦ b ⟧} π'
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  isEquiv-≈ᵗ : IsEquivalence _≈ᵗ_
  isEquiv-≈ᵗ = record
    { refl = ≈refl
    ; sym = ≈sym
    ; trans = ≈trans }

  MobileSetoid : Setoid l0 l0
  MobileSetoid = record
    { Carrier = BTree
    ; _≈_ = _≈ᵗ_
    ; isEquivalence = isEquiv-≈ᵗ }

  open import Plump Branch
    renaming (_≺_ to _<_; ≺sup to <sup)

  data ⊥p : Prop where
  absurdp : {A : Prop} → ⊥p → A
  absurdp ()

  leaf≉node : ∀ {f g} → leaf {g} ≈ᵗ node f → ⊥p
  leaf≉node (≈trans {t = leaf} p q) = leaf≉node q
  leaf≉node (≈trans {t = node _} p q) = leaf≉node p

  -- open import Relation.Binary.Core
  leaf≤leaf : ∀ {f g} → leaf {f} ≤ leaf {g}
  leaf≤leaf = sup≤ (λ ())
  ≤-resp-≈ᵗ : ∀ {x y} → x ≈ᵗ y → x ≤ y
  ≤-resp-≈ᵗ {leaf {f}} {leaf {g}} p = leaf≤leaf 
  ≤-resp-≈ᵗ {leaf} {node f} p = absurdp (leaf≉node p)
  ≤-resp-≈ᵗ {node f} {leaf} p = absurdp (leaf≉node (≈sym p))
  ≤-resp-≈ᵗ {node f} {node g} (≈node c) =
    sup≤ λ b → <sup b ((≤-resp-≈ᵗ (c b)))
  ≤-resp-≈ᵗ {node f} {node g} (≈perm π) =
    sup≤ (λ b → <sup (π.⟦ b ⟧⁻¹) (u b))
    where
    module π = SetoidIso π
    u : ∀ b → f b ≤ f (π.⟦ π.⟦ b ⟧⁻¹ ⟧) 
    u b = q p
      where
      p : ∥ π.⟦ π.⟦ b ⟧⁻¹ ⟧ ≡ b ∥
      p = π.linv b
      q : ∀ (p : ∥ π.⟦ π.⟦ b ⟧⁻¹ ⟧ ≡ b ∥) → f b ≤ f (π.⟦ π.⟦ b ⟧⁻¹ ⟧) 
      q ∣ p ∣ = substp (λ x → f b ≤ f x) (≡.sym p) (≤refl (f b))
  ≤-resp-≈ᵗ {node f} {node g} (≈trans {t = t} p q) =
    ≤≤ {i = node f} {j = t} {k = node g}
       (≤-resp-≈ᵗ q) (≤-resp-≈ᵗ p)

  isPreorder-≤ : IsPreorder MobileSetoid _≤_
  isPreorder-≤ = record
    { refl = ≤-resp-≈ᵗ
    ; trans = λ p q → ≤≤ q p }

  record Sz₀ (t : BTree) : Set l0 where
    constructor sz
    field
      u : BTree
      u<t : u < t

  Sz : BTree → Setoid l0 l0
  Sz t = record
    { Carrier = Sz₀ t
    ; _≈_ = λ (sz u _) (sz s _) → u ≈ᵗ s
    ; isEquivalence = record
      { refl = ≈refl
      ; sym = ≈sym
      ; trans = ≈trans } }

  P : ∀ {t u} → u ≤ t → SetoidHom (Sz u) (Sz t)
  P {t} {u} u≤t = record
    { ⟦_⟧ = λ (sz s s<u) → sz s (≤< u≤t s<u)
    ; cong = λ s≈u → s≈u }

  -- open import Function.Construct.Identity using () renaming (function to identity)

  module ≤ = IsPreorder isPreorder-≤

  Id : ∀ {t : BTree}
     → SetoidHom≈ (P (≤refl t)) idHom 
  Id p = p

  Comp : ∀{s t u} (p : s ≤ t) (q : t ≤ u)
       → SetoidHom≈ (P (≤.trans p q)) (P q ∘ P p)   
  Comp _ _ r = r

  module MobileColim where
    open import Colimit isPreorder-≤ B
    D : Diagram
    D = record
      { D-ob = Sz
      ; D-mor = P
      ; D-id = λ {i} {x} {y} → Id {i} {x} {y}
      ; D-comp = Comp }

    open Colim D

    module ContainerFunctor (C : Container l0 l0) where
      module Ob (S : Setoid l0 l0) where
        open Setoid S 
        record _≈ꟳ_ (x y : ⟦ C ⟧ ⟨ S ⟩) : Prop l0 where
          constructor mk≈ꟳ
          field
            fst≡ : x .proj₁ ≡ y .proj₁
            snd≈ : ∀ p → (x .proj₂) p ≈ (y .proj₂) (subst (C .Position) fst≡ p)

        isReflexive : Reflexive _≈ꟳ_
        isReflexive = mk≈ꟳ ≡.refl (λ p → S .≈.refl)

        isSymmetric : Symmetric _≈ꟳ_
        isSymmetric {x} {y} (mk≈ꟳ fst≡ snd≈) =
          mk≈ꟳ (≡.sym fst≡) λ p → S .≈.sym (snd≈⁻¹ p)
          where
          u : ∀ p → x .proj₂ (subst (C .Position) (≡.sym fst≡) p) ≈
                    y .proj₂ (subst (C .Position) fst≡
                             (subst (C .Position) (≡.sym fst≡) p))
          u p = snd≈ (subst (C .Position) (≡.sym fst≡) p)
          v : ∀ p → (subst (C .Position) fst≡ (subst (C .Position) (≡.sym fst≡) p))
                  ≡ p
          v p = subst-subst-sym fst≡
          snd≈⁻¹ : ∀ p → x .proj₂ (subst (C .Position) (≡.sym fst≡) p) ≈ y .proj₂ p
          snd≈⁻¹ p =
            substp (λ ○ → x .proj₂ (subst (C .Position) (≡.sym fst≡) p) ≈ y .proj₂ ○)
                   (v p) (snd≈ (subst (C .Position) (≡.sym fst≡) p))

        isTransitive : Transitive _≈ꟳ_
        isTransitive {x = x} {y} {z} (mk≈ꟳ fst≡1 snd≈1) (mk≈ꟳ fst≡2 snd≈2) =
          mk≈ꟳ (≡.trans fst≡1 fst≡2) v
          where
          u : ∀ p → x .proj₂ p ≈ z .proj₂ (subst (C .Position) fst≡2 (subst (C .Position) fst≡1 p)) 
          u p = S .≈.trans (snd≈1 p) (snd≈2 (subst (C .Position) fst≡1 p))
          v : ∀ p → x .proj₂ p ≈ z .proj₂ (subst (C .Position) (≡.trans fst≡1 fst≡2) p) 
          v p = substp (λ ○ → x .proj₂ p ≈ z .proj₂ ○) (subst-subst fst≡1) (u p)


        F̃-ob : Setoid l0 l0 
        F̃-ob = record
          { Carrier = ⟦ C ⟧ ⟨ S ⟩
          ; _≈_ = _≈ꟳ_
          ; isEquivalence = record
            { refl = isReflexive
            ; sym = isSymmetric
            ; trans = isTransitive } }

      open Ob using (F̃-ob)

      module Mor {S T : Setoid l0 l0} (f : SetoidHom S T) where
        module S = Setoid S
        module T = Setoid T
        module f = SetoidHom f
        ⟦_⟧h : ⟦ C ⟧ ⟨ S ⟩ → ⟦ C ⟧ ⟨ T ⟩
        ⟦ s , g ⟧h = s , λ x → f.⟦ g x ⟧ 
        congh : ∀ {x y} → (F̃-ob S Setoid.≈ x) y → (T Ob.≈ꟳ ⟦ x ⟧h) ⟦ y ⟧h
        congh (Ob.mk≈ꟳ fst≡ snd≈) = Ob.mk≈ꟳ fst≡ (λ p → f.cong (snd≈ p))
        F̃-mor : SetoidHom (F̃-ob S) (F̃-ob T)
        F̃-mor = record
          { ⟦_⟧ = ⟦_⟧h
          ; cong = congh
          }

      open Mor using (F̃-mor)

      module Comp {S T U : Setoid l0 l0} (f : SetoidHom S T) (g : SetoidHom T U) where
        module S = Setoid S
        module T = Setoid T
        module U = Setoid U
        module f = SetoidHom f
        module g = SetoidHom g

        F̃-comp : SetoidHom≈ (F̃-mor (g ∘ f)) (F̃-mor g ∘ F̃-mor f)
        F̃-comp (Ob.mk≈ꟳ fst≡ snd≈) =
          Ob.mk≈ꟳ fst≡ λ p → g.cong (f.cong (snd≈ p))

      open Comp using (F̃-comp)
      
      F̃ : SetoidFunctor
      F̃ = record
        { F-ob = F̃-ob
        ; F-mor = F̃-mor
        ; F-id = λ p → p
        ; F-comp = F̃-comp }
