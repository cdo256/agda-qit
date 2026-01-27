{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.Mobile.Cocontinuity
  (I : Set) (_ : ∥ I ∥) where

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
open import QIT.QW.StageColimit sig using (joinTerms; αˡ; tˡ; t≤αˡ)

open import QIT.Container.Functor Sᵀ Pᵀ ℓ0 (lsuc ℓ0)

open F-Ob

module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)

private
  L = Colim (F ∘ᴰ D)
  R = F.F-ob (Colim D)

ϕ₀ : ⟨ Colim (F ∘ᴰ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (α , (s , f)) = s , (λ b → α , f b)

ϕ-cong-stage : ∀ α {x y} → F∘D.D-ob α [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ (α , x) ≈ ϕ₀ (α , y) ]
ϕ-cong-stage α {a , f} {a , g} (mk≈ꟳ ≡.refl snd≈) =
  mk≈ꟳ ≡.refl q
  where
  q : (i : Pᵀ a) → Colim D [ α , f i ≈ α , g i ]
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

depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≤≥ ιᶻ (t̂ .fst)
depth-preserving α (s , s≤α) (t , t≤α) (≈pcong a μ f g r) =
    sup≤sup (λ i → p i .∧.fst) , sup≤sup (λ i → p i .∧.snd)
  where p : ∀ i → ιᶻ (f i .fst) ≤≥ ιᶻ (g i .fst)
        p i = depth-preserving (μ i) (f i) (g i) (r i)
depth-preserving α (s , _) (t , _) (≈psat π ϕ _ _) =
    sup≤ (λ i → <sup (π⁻¹ i) (≡→≤ (≡.cong (λ ○ → ιᶻ (ϕ ○)) (≡.sym (linv i)))))
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
ψ₀ (s , f) = sup (ιˢ s , μ) , s , λ i → pweaken (child≤ (ιˢ s) μ i) (f i .proj₂)
  where
  μ : Pᵀ s → Z
  μ i = f i .proj₁

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

module _ (depth-preserving : ∀ α ŝ t̂ → α ⊢ ŝ ≈ᵇ t̂ → ιᶻ (ŝ .fst) ≤≥ ιᶻ (t̂ .fst)) where
  -- tightening
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
  ψ-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = begin
    ψ₀ (s , f)
      ≈⟨ ≈lrefl (F ∘ᴰ D) ⟩
    (αf , s , λ i → tf i , _)
      ≈⟨ ≈lstep ∨ᶻ-l (s , _) ⟩
    (αf ∨ᶻ αg , s , λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ _) (fi≤μi i)))
      ≈⟨ ≈lstage (αf ∨ᶻ αg) (mk≈ꟳ ≡.refl v) ⟩
    (αf ∨ᶻ αg , s , λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ _) (gi≤μi i)))
      ≈⟨ ≈lsym (≈lstep ∨ᶻ-r (s , _)) ⟩
    (αg , s , λ i → tg i , _)
      ≈⟨ ≈lrefl (F ∘ᴰ D) ⟩
    ψ₀ (s , g) ∎
    where
    μf : Pᵀ s → Z
    μf i = f i .proj₁
    μg : Pᵀ s → Z
    μg i = g i .proj₁
    μ : Pᵀ s → Z
    μ i = μf i ∨ᶻ μg i
    αf = sup (ιˢ s , μf)
    αg = sup (ιˢ s , μg)
    α = αf ∨ᶻ αg
    tf : Pᵀ s → T
    tf i = f i .proj₂ .fst
    tg : Pᵀ s → T
    tg i = g i .proj₂ .fst
    fi≤μi : ∀ i → tf i ≤ᵀ μf i
    fi≤μi i = f i .proj₂ .snd
    gi≤μi : ∀ i → tg i ≤ᵀ μg i
    gi≤μi i = g i .proj₂ .snd
    v : ∀ i → α ⊢ (tf i  , _) ≈ᵇ (tg i , _)
    v i = ≈pweaken (≤≤ μi≤α (≤≤ ∨ᶻ-l (fi≤μi i))) (≈ˡ→≈ˢ (snd≈ i) .≈s.s≈t)
      where
      μi≤α : μ i ≤ α
      μi≤α = ∨ᶻ≤ (<≤ ∨ᶻ-l< (child≤ (ιˢ s) μf i)) (<≤ ∨ᶻ-r< (child≤ (ιˢ s) μg i))
    open ≈.Hom
    open Setoid (Colim (F ∘ᴰ D))
    open ≈.≈syntax {S = Colim (F ∘ᴰ D)}

linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
linv (s , g) =
  ϕ₀ (ψ₀ (s , g))
    ≈⟨ ≈frefl (Colim D) ⟩
  (s , λ i → sup (ιˢ s , λ i → g i .proj₁) , pweaken (child≤ (ιˢ s) μ i) (g i .proj₂))
    ≈⟨ mk≈ꟳ ≡.refl (λ i → ≈lsym (≈lstep (child≤ (ιˢ s) μ i) (g i .proj₂))) ⟩
  (s , λ i → g i .proj₁ , g i .proj₂) ∎
  where
  μ : Pᵀ s → Z
  μ i = g i .proj₁
  open Setoid (F.F-ob (Colim D))
  open Diagram D
  open ≈.≈syntax {S = (F.F-ob (Colim D))}

rinv : ∀ x → Colim (F ∘ᴰ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
rinv (α , (s , g)) = begin
  ψ₀ (ϕ₀ (α , (s , g)))
    ≈⟨ refl ⟩
  α' , (s , λ i → pweaken (child≤ (ιˢ s) (λ _ → α) i) (g i))
    ≈⟨ (≈lstep ∨ᶻ-r (s , (λ i → pweaken ((child≤ (ιˢ s) (λ _ → α) i)) (g i)))) ⟩
  α ∨ᶻ α' , (s , λ i → pweaken (≤≤ ∨ᶻ-r (child≤ (ιˢ s) (λ _ → α) i)) (g i))
    ≈⟨ refl ⟩
  α ∨ᶻ α' , (s , λ i → pweaken ∨ᶻ-l (g i))
    ≈⟨ sym (≈lstep ∨ᶻ-l (s , g)) ⟩
  α , (s , g) ∎
  where
  α' = sup (ιˢ s , λ _ → α)
  β = α ∨ᶻ α'
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
    ; cong⁻¹ = ψ-cong depth-preserving
    ; linv = linv
    ; rinv = rinv
    }
