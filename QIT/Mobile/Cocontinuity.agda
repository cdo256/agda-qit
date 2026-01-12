{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.Mobile.Cocontinuity
  (I : Set) (inhabI : ∥ I ∥) where

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Mobile.Base I
open import QIT.Setoid as ≈
open import QIT.Container.Base
open import QIT.Relation.Plump Sᵀ Pᵀ
open import QIT.Setoid.Diagram ≤p

open import QIT.QW.Colimit ≤p ℓ0 (lsuc ℓ0) hiding (_≈ˡ_)
open import QIT.QW.Cocontinuity ≤p
open import QIT.QW.Stage sig

open import QIT.Container.Functor Sᵀ Pᵀ ℓ0 (lsuc ℓ0)

open F-Ob

module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)

private
  L = Colim (F ∘ᴰ D)
  R = F.F-ob (Colim D)

ϕ₀ : ⟨ Colim (F ∘ᴰ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (α , (l , _)) = l , (λ ())
ϕ₀ (α , (n , f)) = n , (λ b → α , f b)

ϕ-cong-stage : ∀ α {x y} → F∘D.D-ob α [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ (α , x) ≈ ϕ₀ (α , y) ]
ϕ-cong-stage α {l , f} {l , g} (mk≈ꟳ ≡.refl snd≈) =
  mk≈ꟳ ≡.refl λ()
ϕ-cong-stage α {n , f} {n , g} (mk≈ꟳ ≡.refl snd≈) =
  mk≈ꟳ ≡.refl q
  where
  q : (i : I) → Colim D [ α , f i ≈ α , g i ]
  q i = ≈lstage α u
    where
    u :  α ⊢ f i ≈ᵇ g i
    u = snd≈ i

ϕ-cong : ∀ {x y} → Colim (F ∘ᴰ D) [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
ϕ-cong (≈lstage α e) = ϕ-cong-stage α e
ϕ-cong (≈lstep {α} {j} p (l , _)) = mk≈ꟳ ≡.refl λ()
ϕ-cong (≈lstep {α} {j} (sup≤ p) (n , f)) =
  mk≈ꟳ ≡.refl λ k → ≈lstep (sup≤ p) (f k)
ϕ-cong (≈lsym p) = ≈fsym (Colim D) (ϕ-cong p)
ϕ-cong (≈ltrans p q) = ≈ftrans (Colim D) (ϕ-cong p) (ϕ-cong q)

node≢leaf : ∀ {f g} → _≡_ {A = T} (sup (n , f)) (sup (l , g)) → ⊥p
node≢leaf ()

n≢l : n ≡p l → ⊥p
n≢l ∣ () ∣

shape : T → Sᵀ
shape (sup (s , _)) = s

shape-preserved : ∀ α s t → α ⊢ s ≈ᵇ t → shape (s .fst) ≡p shape (t .fst)
shape-preserved α s t (≈pcong a μ f g r) = reflp
shape-preserved α s t (≈psat e ϕ l≤α r≤α) = reflp
shape-preserved α s t ≈prefl = reflp
shape-preserved α s t (≈psym s≈t) = symp (shape-preserved α t s s≈t)
shape-preserved α s t (≈ptrans {t̂ = u} s≈u u≈t) =
  transp (shape-preserved α s u s≈u) (shape-preserved α u t u≈t)
shape-preserved α s t (≈pweaken α≤β s≈t) = shape-preserved _ _ _ s≈t

node≉ᵇleaf : ∀ α {f g} s t → sup (n , f) ≡ s .fst → sup (l , g) ≡ t .fst → α ⊢ s ≈ᵇ t → ⊥p
node≉ᵇleaf α s t f̂≡s ĝ≡t s≈t = n≢l (substp₂ (λ s t → shape s ≡p shape t) (≡.sym f̂≡s) (≡.sym ĝ≡t)
                                            (shape-preserved α s t s≈t))

depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≤≥ ιᶻ (t̂ .fst)
depth-preserving α (s , s≤α) (t , t≤α) (≈pcong a μ f g r) =
    sup≤sup (λ i → p i .∧.fst) , sup≤sup (λ i → p i .∧.snd)
  where p : ∀ i → ιᶻ (f i .fst) ≤≥ ιᶻ (g i .fst)
        p i = depth-preserving (μ i) (f i) (g i) (r i)
depth-preserving α (s , _) (t , _) (≈psat π ϕ _ _) =
    sup≤ (λ i → <sup (π⁻¹ i) (substp (λ ○ → ιᶻ (ϕ i) ≤ ιᶻ (ϕ ○)) (≡.sym (linv i)) (≤refl (ιᶻ (ϕ i)))))
  , sup≤ (λ i → <sup (π̂ i) (≤refl (ιᶻ (ϕ (π̂ i)))))
  where
  open _↔_ π renaming (to to π̂; from to π⁻¹)
depth-preserving α (s , s≤α) (s , t≤α) ≈prefl = ≤refl (ιᶻ s) , ≤refl (ιᶻ s)
depth-preserving α (s , s≤α) (t , t≤α) (≈psym p) =
  let s≤t , t≤s = depth-preserving α (t , t≤α) (s , s≤α) p
  in t≤s , s≤t
depth-preserving α (s , s≤α) (t , t≤α) (≈ptrans {t̂ = u , u≤α} p q) =
  let s≤u , u≤s = depth-preserving α (s , s≤α) (u , u≤α) p
      u≤t , t≤u = depth-preserving α (u , u≤α) (t , t≤α) q
  in ≤≤ u≤t s≤u , ≤≤ u≤s t≤u
depth-preserving α (s , s≤α) (t , t≤α) (≈pweaken {α = β} β≤α p) = depth-preserving β _ _ p

ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F ∘ᴰ D) ⟩
ψ₀ (l , _) = ⊥ᶻ , l , λ()
ψ₀ (n , f) = sup (ιˢ n , μ) , n , λ i → pweaken (child≤ (ιˢ n) μ i) (f i .proj₂)
  where
  μ : I → Z
  μ i = f i .proj₁

leaf≈leaf : ∀ α {f g f≤α g≤α} 
          → α ⊢ sup (l , f) , f≤α ≈ᵇ sup (l , g) , g≤α
leaf≈leaf α {f} {g} {f≤α} {g≤α} = ≡→≈ (D̃ α) (ΣP≡ _ _ (leaf≡leaf f g)) 

_≤≥ᵀ_ : ∀ (s t : T) → Prop _
s ≤≥ᵀ t = ιᶻ s ≤≥ ιᶻ t

module ≈s where
  record _≈ˢ_ (s t : T) : Prop _ where
    constructor mk≈ˢ
    field
      s≤≥t : ιᶻ s ≤≥ ιᶻ t
      s≈t : ιᶻ s ⊢ s , ≤refl (ιᶻ s) ≈ᵇ t , s≤≥t .∧.snd
  open _≈ˢ_ public
open ≈s hiding (s≤≥t; s≈t)

≈srefl : ∀ {s} → s ≈ˢ s
≈srefl {s} = mk≈ˢ ≤≥-refl ≈prefl

≈ssym : ∀ {s t} → s ≈ˢ t → t ≈ˢ s
≈ssym (mk≈ˢ s≤≥t s≈t) = mk≈ˢ (≤≥-sym s≤≥t) (≈psym (≈pweaken (s≤≥t .∧.fst) s≈t))

≈strans : ∀ {s t u} → s ≈ˢ t → t ≈ˢ u → s ≈ˢ u
≈strans (mk≈ˢ s≤≥t s≈t) (mk≈ˢ t≤≥u t≈u) = mk≈ˢ (≤≥-trans s≤≥t t≤≥u) (≈ptrans s≈t (≈pweaken (s≤≥t .∧.snd) t≈u))

≈scong : ∀ a (f g : ∀ i → T)
       → (r : ∀ i → f i ≈ˢ g i)
       → sup (a , f) ≈ˢ sup (a , g)
≈scong a f g r = mk≈ˢ (≤≥-cong (ιˢ a) (λ α → ιᶻ (f α)) (λ α → ιᶻ (g α)) λ i → r i .≈s.s≤≥t)
                      (≈pcong a (λ α → ιᶻ (f α))
                                (λ i → f i , ≤refl _)
                                (λ i → g i , r i .≈s.s≤≥t .∧.snd)
                                (λ i → r i .≈s.s≈t))

≈ᵇ→≈ˢ : ∀ {α ŝ t̂} → D̃ α [ ŝ ≈ t̂ ]
     → ŝ .fst ≈ˢ t̂ .fst
≈ᵇ→≈ˢ {α} {s , s≤α} {t , t≤α} p = u p
  where
  u : D̃ α [ s , s≤α ≈ t , t≤α ]
    → s ≈ˢ t
  u (≈pcong a μ f g r) = ≈scong a (λ i → f i .fst) (λ i → g i .fst) (λ i → ≈ᵇ→≈ˢ (r i))
  u (≈psat π ϕ l≤α r≤α) = mk≈ˢ s≤≥t (≈psat π ϕ (≤refl (ιᶻ (lhs' π ϕ))) _)
    where
    s≤≥t : s ≤≥ᵀ t
    s≤≥t = depth-preserving α (sup (n , ϕ) , s≤α) (sup (n , ϕ ∘ᵗ π) , t≤α) p
  u ≈prefl = ≈srefl
  u (≈psym p) = ≈ssym (≈ᵇ→≈ˢ p)
  u (≈ptrans p q) = ≈strans (≈ᵇ→≈ˢ p) (≈ᵇ→≈ˢ q)
  u (≈pweaken _ p) = (≈ᵇ→≈ˢ p)


≈ˡ→≈ˢ : ∀ {ŝ t̂} → Colim D [ ŝ ≈ t̂ ]
     → ŝ .proj₂ .fst ≈ˢ t̂ .proj₂ .fst
≈ˡ→≈ˢ {α , s , s≤α} {α , t , t≤α} (≈lstage α p) = ≈ᵇ→≈ˢ p
≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈lstep p x) = ≈srefl
≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈lsym p) = ≈ssym (≈ˡ→≈ˢ p)
≈ˡ→≈ˢ {α , s , s≤α} {β , t , t≤β} (≈ltrans p q) = ≈strans (≈ˡ→≈ˢ p) (≈ˡ→≈ˢ q)

ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ] → Colim (F ∘ᴰ D) [ ψ₀ x ≈ ψ₀ y ]
ψ-cong {l , f} {l , g} (mk≈ꟳ ≡.refl snd≈) = ≈lrefl (F ∘ᴰ D)
ψ-cong {n , f} {n , g} (mk≈ꟳ ≡.refl snd≈) = begin
  ψ₀ (n , f)
    ≈⟨ ≈lrefl (F ∘ᴰ D) ⟩
  (αf , n , λ i → tf i , _)
    ≈⟨ ≈lstep ∨ᶻ-l (n , _) ⟩
  (αf ∨ᶻ αg , n , λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ _) (fi≤μi i)))
    ≈⟨ ≈lstage (αf ∨ᶻ αg) inner ⟩
  (αf ∨ᶻ αg , n , λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ _) (gi≤μi i)))
    ≈⟨ ≈lsym (≈lstep ∨ᶻ-r (n , _)) ⟩
  (αg , n , λ i → tg i , _)
    ≈⟨ ≈lrefl (F ∘ᴰ D) ⟩
  ψ₀ (n , g) ∎
  where
  μf : I → Z
  μf i = f i .proj₁
  μg : I → Z
  μg i = g i .proj₁
  μ : I → Z
  μ i = μf i ∨ᶻ μg i
  αf = sup (ιˢ n , μf)
  αg = sup (ιˢ n , μg)
  α = αf ∨ᶻ αg
  tf : I → T
  tf i = f i .proj₂ .fst
  tg : I → T
  tg i = g i .proj₂ .fst
  fi≤μi : ∀ i → tf i ≤ᵀ μf i
  fi≤μi i = f i .proj₂ .snd
  gi≤μi : ∀ i → tg i ≤ᵀ μg i
  gi≤μi i = g i .proj₂ .snd
  inner : F.F-ob (D.D-ob α) [ n , (λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ i) (fi≤μi i)))
                            ≈ n , (λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ i) (gi≤μi i))) ]
  inner = mk≈ꟳ ≡.refl λ i → v i
    where
    u : ∀ i → Colim D [ f i ≈ g i ] → μf i ∨ᶻ μg i ⊢ (tf i  , ≤≤ ∨ᶻ-l (fi≤μi i)) ≈ᵇ (tg i , ≤≤ ∨ᶻ-r (gi≤μi i)) 
    u i p = ≈pweaken q (≈ˡ→≈ˢ (snd≈ i) .≈s.s≈t)
      where
      q : ιᶻ (f i .proj₂ .fst) ≤ μf i ∨ᶻ μg i
      q = ≤≤ ∨ᶻ-l (fi≤μi i)
    v : ∀ i → α ⊢ (tf i  , _) ≈ᵇ (tg i , _) 
    v i = ≈pweaken μi≤α (u i (snd≈ i))
      where
      μi≤α : μ i ≤ α
      μi≤α = ∨ᶻ≤ (<≤ ∨ᶻ-l< (child≤ (ιˢ n) μf i)) (<≤ ∨ᶻ-r< (child≤ (ιˢ n) μg i))
  open ≈.Hom
  open Setoid (Colim (F ∘ᴰ D))
  open ≈.≈syntax {S = Colim (F ∘ᴰ D)}

linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
linv (l , f) = begin
  ϕ₀ (ψ₀ (l , f))
    ≈⟨ refl ⟩
  (l , λ ())
    ≈⟨ mk≈ꟳ ≡.refl (λ ()) ⟩
  (l , f) ∎
  where
    open ≈.≈syntax {S = (F.F-ob (Colim D))}
    open Setoid (F.F-ob (Colim D))
linv (n , g) =
  ϕ₀ (ψ₀ (n , g))
    ≈⟨ ≈frefl (Colim D) ⟩
  (n , λ i → sup (ιˢ n , λ i → g i .proj₁) , pweaken (child≤ (ιˢ n) μ i) (g i .proj₂))
    ≈⟨ mk≈ꟳ ≡.refl (λ i → ≈lsym (≈lstep (child≤ (ιˢ n) μ i) (g i .proj₂))) ⟩
  (n , λ i → g i .proj₁ , g i .proj₂) ∎
  where
  μ : I → Z
  μ i = g i .proj₁
  open Setoid (F.F-ob (Colim D))
  open Diagram D
  open ≈.≈syntax {S = (F.F-ob (Colim D))}

child≤node-const : ∀ α → α ≤ sup (ιˢ n , λ _ → α)
child≤node-const α = f inhabI
  where
  f : ∥ I ∥ → α ≤ sup (ιˢ n , (λ _ → α))
  f ∣ i ∣ = child≤ (ιˢ n) (λ _ → α) i

rinv : ∀ x → Colim (F ∘ᴰ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
rinv (α , (l , f)) = begin
  ψ₀ (ϕ₀ (α , (l , f)))
    ≈⟨ ≈lstage ⊥ᶻ (≈frefl (D.D-ob ⊥ᶻ)) ⟩
  ⊥ᶻ , (l , λ ())
    ≈⟨ ≈lstep (sup≤ (λ ())) (l , (λ ())) ⟩
  α , (l , λ ())
    ≈⟨ ≈lstage α (mk≈ꟳ ≡.refl λ ()) ⟩
  α , (l , f) ∎
  where
  open Setoid (Colim (F ∘ᴰ D))
  open ≈.≈syntax {S = Colim (F ∘ᴰ D)}
rinv (α , (n , g)) = begin
  ψ₀ (ϕ₀ (α , (n , g)))
    ≈⟨ refl ⟩
  sup (ιˢ n , λ _ → α) , (n , λ i → pweaken (child≤ (ιˢ n) (λ _ → α) i) (g i))
    ≈⟨ ≈lsym (≈lstep (child≤node-const α) (n , g)) ⟩
  α , (n , g) ∎
  where
  open Setoid (Colim (F ∘ᴰ D))
  open ≈.≈syntax {S = Colim (F ∘ᴰ D)}

cocontinuous : Cocontinuous F D
cocontinuous = ∣ iso ∣
  where
  iso : ≈.Iso (Colim (F ∘ᴰ D)) (F.F-ob (Colim D))
  iso = record
    { ⟦_⟧ = ϕ₀
    ; ⟦_⟧⁻¹ = ψ₀
    ; cong = ϕ-cong
    ; cong⁻¹ = ψ-cong
    ; linv = linv
    ; rinv = rinv
    }
