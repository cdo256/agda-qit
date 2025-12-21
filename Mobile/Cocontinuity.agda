{-# OPTIONS --type-in-type #-}
module Mobile.Cocontinuity (B : Set) where

open import Prelude
open import Equivalence
open import Mobile.Base B
open import Mobile.Equivalence B
open import Mobile.Colimit B
open import Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Container hiding (_⇒_; identity; refl; sym; trans)
open import Data.Unit
open import Data.Sum
open import Plump Branch

private
  l0 : Level
  l0 = lzero

open import Colimit ≤p
open Colim
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
  Ob.mk≈ꟳ ≡.refl λ b → {!≈lstage i (u b)!}
  where
  open ≈.≈syntax {S = Colim D}
  open Colim D
  s : ∀ b → f b .Sz₀.u ≈ᵗ g b .Sz₀.u
  s b = substp (λ ○ → f b .Sz₀.u ≈ᵗ g ○ .Sz₀.u) (subst-id fst≡ b) (snd≈ b)
  u : ∀ b → Sz i [ f b ≈ g b ]
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


