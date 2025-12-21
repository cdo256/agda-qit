{-# OPTIONS --type-in-type #-}
module Mobile where

open import Prelude
open import Equivalence
open import Data.Product
-- open import Function.Bundles
open import Function.Definitions
-- open import Relation.Binary.PropositionalEquality as ≡
open import Setoid as ≈
open import Function.Properties.Inverse 
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)
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
    ≈leaf : leaf ≈ᵗ leaf
    ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
          → node f ≈ᵗ node g
    ≈perm : ∀ {f} → (π : ≈.Iso Bˢ Bˢ)
          → node f ≈ᵗ node λ b → f (≈.Iso.⟦_⟧ π b)
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
    module π = ≈.Iso π
    π' = ≈.IsoFlip π
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

  ⊥→⊥p : ⊥ → ⊥p
  ⊥→⊥p ()

  leaf≉node : ∀ {f g} → leaf {g} ≈ᵗ node f → ⊥p
  leaf≉node (≈trans {t = leaf} p q) = leaf≉node q
  leaf≉node (≈trans {t = node _} p q) = leaf≉node p

  l≢n : l ≡ n → ⊥p
  l≢n ()

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
    module π = ≈.Iso π
    u : ∀ b → f b ≤ f (π.⟦ π.⟦ b ⟧⁻¹ ⟧) 
    u b = q p
      where
      p : π.⟦ π.⟦ b ⟧⁻¹ ⟧ ≡p b
      p = π.linv b
      q : ∀ (p : π.⟦ π.⟦ b ⟧⁻¹ ⟧ ≡p b) → f b ≤ f (π.⟦ π.⟦ b ⟧⁻¹ ⟧) 
      q ∣ p ∣ = substp (λ x → f b ≤ f x) (≡.sym p) (≤refl (f b))
  ≤-resp-≈ᵗ {node f} {node g} (≈trans {t = t} p q) =
    ≤≤ {i = node f} {j = t} {k = node g}
       (≤-resp-≈ᵗ q) (≤-resp-≈ᵗ p)

  isPreorder-≤ : IsPreorder MobileSetoid _≤_
  isPreorder-≤ = record
    { refl = ≤-resp-≈ᵗ
    ; trans = λ p q → ≤≤ q p }

  ≤p : Preorder MobileSetoid _
  ≤p = _≤_ , isPreorder-≤

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

  P : ∀ {t u} → u ≤ t → ≈.Hom (Sz u) (Sz t)
  P {t} {u} u≤t = record
    { ⟦_⟧ = λ (sz s s<u) → sz s (≤< u≤t s<u)
    ; cong = λ s≈u → s≈u }

  -- open import Function.Construct.Identity using () renaming (function to identity)

  module ≤ = IsPreorder isPreorder-≤

  Id : ∀ {t : BTree}
     → ≈.Hom≈ (P (≤refl t)) ≈.idHom 
  Id p = p

  Comp : ∀{s t u} (p : s ≤ t) (q : t ≤ u)
       → ≈.Hom≈ (P (≤.trans p q)) (P q ≈.∘ P p)   
  Comp _ _ r = r

  module MobileColim where
    open import Colimit ≤p
    D : Diagram
    D = record
      { D-ob = Sz
      ; D-mor = P
      ; D-id = λ {i} {x} {y} → Id {i} {x} {y}
      ; D-comp = Comp }

    open Colim D

  open MobileColim

  module Cocontinuity where
    open import Colimit ≤p
    open Colim hiding (≈j)
    open import ContainerFunctor Branch
    open import Cocontinuity ≤p 

    module F = ≈.Functor F̃
    module D = Diagram D
    open ≈.Hom
    ϕ₀ : ⟨ Colim (F̃ ∘ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
    ϕ₀ (i , (l , _)) = l , (λ ())
    ϕ₀ (i , (n , f)) = n , (λ b → i , f b)

    ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F̃ ∘ D) ⟩
    ψ₀ (l , _) = sup (l , (λ ())) , l , (λ ())
    ψ₀ (n , f) = sup (n , g) , (n , h)
      where
      g : B → ⟨ MobileSetoid ⟩
      g b = f b .proj₁
      h : B → ⟨ D.D-ob (node g) ⟩
      h b = sz (g b) gb<ng
        where
        gb<ng : g b < node g
        gb<ng = <sup b (≤refl (g b))

    l≉ꟳn : ∀ {f g} → Ob._≈ꟳ_ (Colim D) (l , f) (n , g) → ⊥p
    l≉ꟳn ∣ () ∣

    ϕ-cong : ∀ {x y} → Colim (F̃ ∘ D) [ x ≈ y ]
           → F.F-ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
    -- ϕ-cong {i , s , f} {i , t , g} (≈lstage _ (Ob.mk≈ꟳ fst≡ snd≈)) = Ob.mk≈ꟳ {!!} {!!}
    ϕ-cong {i , l , f} {i , l , g} (≈lstage _ (Ob.mk≈ꟳ fst≡ snd≈)) = Ob.mk≈ꟳ fst≡ λ ()
    ϕ-cong {i , n , f} {i , l , g} (≈lstage _ (Ob.mk≈ꟳ fst≡ snd≈)) =
      absurdp (l≢n (≡.sym fst≡))
    ϕ-cong {i , l , f} {i , n , g} (≈lstage _ (Ob.mk≈ꟳ fst≡ snd≈)) =
      absurdp (l≢n fst≡)
    ϕ-cong {i , n , f} {i , n , g} (≈lstage _ (Ob.mk≈ꟳ fst≡ snd≈)) =
      Ob.mk≈ꟳ ≡.refl λ b → ≈lstage i (u b)
      where
      open ≈.≈syntax {S = Colim D}
      open Colim D using (≈j)
      s : ∀ b → f b .Sz₀.u ≈ᵗ g b .Sz₀.u
      s b = substp (λ ○ → f b .Sz₀.u ≈ᵗ g ○ .Sz₀.u) (subst-id fst≡ b) (snd≈ b)
      u : ∀ b → ? [ f b ≈ g b ]
      u b = s b
    ϕ-cong {i , l , _} {j , l , _} (≈lstep p (l , _)) = F.F-id (Ob.mk≈ꟳ ≡.refl (λ ()))
    ϕ-cong {i , n , f} {j , n , g} (≈lstep p (n , f)) =
      Ob.mk≈ꟳ ≡.refl (λ q → ≈lstep p (f q))
    ϕ-cong {i , l , f} {j , l , g} (≈lsym s≈t) = ϕ-cong s≈t
    ϕ-cong {i , l , f} {j , n , g} (≈lsym s≈t) = absurdp (l≉ꟳn u)
      where
      u : (F.F-ob (Colim D) Setoid.≈ ϕ₀ (i , l , f)) (ϕ₀ (j , n , g))
      u = (Setoid.sym (F.F-ob (Colim D)) (ϕ-cong s≈t))
    ϕ-cong {i , n , f} {j , l , g} (≈lsym s≈t) = absurdp (l≉ꟳn (ϕ-cong s≈t))
    ϕ-cong {i , n , f} {j , n , g} (≈lsym s≈t) = Ob.mk≈ꟳ ≡.refl (u v)
      where
      _≈'_ = _≈ˡ_ D
      _≈F_ = _≈ˡ_ (F̃ ∘ D)
      -- v : F.F-ob (Colim D) [ n , (λ b → j , g b) ≈ n , (λ b → i , f b) ]
      v : (Ob._≈ꟳ_ (Colim D) (n , (λ b → j , g b)) (n , (λ b → i , f b)))
      v = ϕ-cong s≈t
      u : (Ob._≈ꟳ_ (Colim D) (n , (λ b → j , g b)) (n , (λ b → i , f b)))
        → (b : B) → (i , f b) ≈' (j , g b)
      u (mk≈ꟳ ≡.refl snd≈) b = ≈lsym (snd≈ b)
    ϕ-cong {i , l , f} {k , l , h} (≈ltrans {t = j , t , g} s≈t t≈u)
      with (ϕ-cong s≈t) | (ϕ-cong t≈u)
    ... | mk≈ꟳ fst≡1 snd≈1 | mk≈ꟳ fst≡2 snd≈2 =
      mk≈ꟳ w λ{ (lift ()) }
      where
      w : ϕ₀ (i , l , f) .proj₁ ≡ ϕ₀ (k , l , h) .proj₁
      w = ≡.trans fst≡1 fst≡2
    ϕ-cong {i , n , f} {k , l , h} (≈ltrans {t = j , t , g} s≈t t≈u)
      with (ϕ-cong s≈t) | (ϕ-cong t≈u)
    ... | mk≈ꟳ fst≡1 snd≈1 | mk≈ꟳ fst≡2 snd≈2 =
      absurdp (l≢n (≡.sym (≡.trans fst≡1 fst≡2)))
    ϕ-cong {i , l , f} {k , n , h} (≈ltrans {t = j , t , g} s≈t t≈u)
      with (ϕ-cong s≈t) | (ϕ-cong t≈u)
    ... | mk≈ꟳ fst≡1 snd≈1 | mk≈ꟳ fst≡2 snd≈2 =
      absurdp (l≢n ((≡.trans fst≡1 fst≡2)))
    ϕ-cong {i , n , f} {k , n , h} (≈ltrans {t = j , t , g} s≈t t≈u)
      with (ϕ-cong s≈t) | (ϕ-cong t≈u)
    ... | mk≈ꟳ fst≡1 snd≈1 | mk≈ꟳ fst≡2 snd≈2 =
      mk≈ꟳ w v
      where
      w : ϕ₀ (i , n , f) .proj₁ ≡ ϕ₀ (k , n , h) .proj₁
      w = ≡.trans fst≡1 fst≡2
      Pos = Branch .Position
      v : ∀ b → Colim D [ ϕ₀ (i , n , f) .proj₂ b
                        ≈ ϕ₀ (k , n , h) .proj₂ (subst Pos w b) ]
      v b = begin
          ϕ₀ (i , n , f) .proj₂ b
            ≈⟨ C.refl ⟩
          (i , f b)
            ≈⟨ ≈ltrans (snd≈1 b) (snd≈2 (subst Pos fst≡1 b)) ⟩
          ϕ₀ (k , n , h) .proj₂ (subst Pos fst≡2 (subst Pos fst≡1 b))
            ≈⟨ ≡→≈ (Colim D) (≡.cong (ϕ₀ (k , n , h) .proj₂) (≡.subst-subst fst≡1)) ⟩
          ϕ₀ (k , n , h) .proj₂ (subst Pos (≡.trans fst≡1 fst≡2) b) ∎
        where
        module C = Setoid (Colim D)
        open ≈.≈syntax {S = Colim D}
    ϕ : ≈.Hom (Colim (F̃ ∘ D)) (F.F-ob (Colim D))
    ϕ = record
      { ⟦_⟧ = ϕ₀
      ; cong = ϕ-cong }

    ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ]
           → Colim (F̃ ∘ D) [ ψ₀ x ≈ ψ₀ y ]
    ψ-cong {l , _} {l , _} (mk≈ꟳ fst≡ snd≈) =
      ≡→≈ (Colim (F̃ ∘ D)) ≡.refl
    ψ-cong {l , _} {n , _} (mk≈ꟳ fst≡ snd≈) =
      absurdp (l≢n fst≡)
    ψ-cong {n , _} {l , _} (mk≈ꟳ fst≡ snd≈) =
      absurdp (l≢n (≡.sym fst≡))
    ψ-cong {n , f1} {n , f2} (mk≈ꟳ ≡.refl snd≈) =
      begin
      ψ₀ (n , f1)
        ≈⟨ C.refl ⟩
      sup (n , g1) , (n , h1)
        ≈⟨ {!!} ⟩
      sup (n , g2) , (n , h2)
        ≈⟨ C.refl ⟩
      ψ₀ (n , f2) ∎
      where
      module C = Setoid (Colim (F̃ ∘ D))
      module M = Setoid MobileSetoid
      open ≈.≈syntax {S = Colim (F̃ ∘ D)}
      g1 : B → ⟨ MobileSetoid ⟩
      g1 b = f1 b .proj₁
      h1 : B → ⟨ D.D-ob (sup (n , g1)) ⟩
      h1 b = sz (g1 b) (<sup b (≤refl (g1 b)))
      g2 : B → ⟨ MobileSetoid ⟩
      g2 b = f2 b .proj₁
      h2 : B → ⟨ D.D-ob (sup (n , g2)) ⟩
      h2 b = sz (g2 b) (<sup b (≤refl (g2 b)))
      Pos = Branch .Position
      r : ∀ b → (p : Colim D [ f1 b ≈ f2 b ])
        → {!Colim (F̃ ∘ D) [ sup (n , g1) , (n , h1)
                        ≈ sup (n , g2) , (n , h2) ]!}
      r b p = {!!}

    cocontinuous : Cocontinuous F̃ D
    cocontinuous = {!!}


