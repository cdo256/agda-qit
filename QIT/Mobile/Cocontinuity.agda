{-# OPTIONS --lossy-unification #-}
open import QIT.Prelude

module QIT.Mobile.Cocontinuity
  (B : Set) (inhabB : ∥ B ∥) (_≟_ : Discrete B)
  (b₁ b₂ : B) (b₁≢b₂ : b₁ ≡.≢ b₂)  where 

open import QIT.Relation.Binary
open import QIT.Mobile.Base B
open import QIT.Mobile.Diagram B inhabB
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import Data.W
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import QIT.Relation.Plump Branch

private
  l0 : Level
  l0 = lzero

open import QIT.Diagram ≤p hiding (_≤_)
open import QIT.Colimit ≤p
open import QIT.Cocontinuity ≤p
open import QIT.Mobile.Functor B

module F = ≈.Functor F̃
module D = Diagram D

private
  L = Colim (F̃ ∘ D)
  R = F.F-ob (Colim D)

ϕ₀ : ⟨ Colim (F̃ ∘ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (i , (l , _)) = l , (λ ())
ϕ₀ (i , (n , f)) = n , (λ b → i , f b)

{-# TERMINATING #-}
ϕ-cong : ∀ {x y} → Colim (F̃ ∘ D) [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
ϕ-cong (≈lstage i ≈leaf) = ≈leaf
ϕ-cong (≈lstage i (≈node c)) = ≈node λ b → ≈lstage i (c b)
ϕ-cong (≈lstage i (≈perm π)) = ≈perm π
ϕ-cong (≈lstage i {u , x} {v , x'} (≈trans {t = w , z} p q)) =
  ≈trans α β
  where
  α = ϕ-cong (≈lstage i p)
  β = ϕ-cong (≈lstage i q)
ϕ-cong (≈lstep {i} {j} p (l , _)) = ≈leaf
ϕ-cong (≈lstep {i} {j} (sup≤ p) (n , f)) = ≈node λ b → ≈lstep (sup≤ p) (f b)
ϕ-cong (≈lsym p) = ≈sym (Colim D) (ϕ-cong p)
ϕ-cong (≈ltrans p q) = ≈trans (ϕ-cong p) (ϕ-cong q)

ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F̃ ∘ D) ⟩
ψ₀ (l , _) = 𝟘 , (l , λ ())
ψ₀ (n , g) = t* , (n , h)
  where
  open Diagram D
  t : B → BTree
  t b = g b .proj₁
  f : ∀ b → P₀ (t b)
  f b = g b .proj₂
  t* : BTree
  t* = sup (n , t) 
  h : ∀ b → ⟨ D-ob t* ⟩
  h b = h'.to (f b)
    where 
    tb≤t* : t b ≤ t*
    tb≤t* = <→≤ (<sup b (≤refl (t b)))
    h' : ≈.Hom (D-ob (t b)) (D-ob t*)
    h' = D-mor tb≤t*
    module h' = ≈.Hom h'

module _ {ℓA} {A : Set ℓA} (s t u : A) where
  fork : B → A
  fork b =
    if (b ≟ b₁)
    then s
    else if (b ≟ b₂)
      then t
      else u

  forkᵗ-l : fork b₁ ≡ s
  forkᵗ-l with (b₁ ≟ b₁)
  ... | yes _ = ≡.refl
  ... | no ¬q = absurd (¬q ≡.refl)
  forkᵗ-r : fork b₂ ≡ t
  forkᵗ-r with (b₂ ≟ b₁) | (b₂ ≟ b₂)
  ... | yes b₂≡b₁ | _ = absurd (b₁≢b₂ (≡.sym b₂≡b₁))
  ... | no _ | yes _ = ≡.refl
  ... | no _ | no ¬r = absurd (¬r ≡.refl)

_∨ᵗ_ : (s t : BTree) → BTree
s ∨ᵗ t = sup (n , fork s t 𝟘)

∨ᵗ-l : ∀ s t → s ≤ s ∨ᵗ t
∨ᵗ-l (sup (s , f)) (sup (t , g)) =
  sup≤ λ b → <sup b₁ (substp (f b ≤_) (≡.sym (forkᵗ-l (sup (s , f)) (sup (t , g)) 𝟘)) (fi≤sup s f b))

∨ᵗ-r : ∀ s t → t ≤ s ∨ᵗ t
∨ᵗ-r (sup (s , f)) (sup (t , g)) =
  sup≤ λ b → <sup b₂ (substp (g b ≤_) (≡.sym (forkᵗ-r (sup (s , f)) (sup (t , g)) 𝟘)) (fi≤sup t g b))

ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ] → Colim (F̃ ∘ D) [ ψ₀ x ≈ ψ₀ y ]
ψ-cong ≈leaf = ≈lstage 𝟘 ≈leaf
ψ-cong (≈node {f} {g} c) = begin
  nf , (n , λ b → weaken (f1 b) nf (fi≤sup n f1 b) (f2 b))
    ≈⟨ ≈lstep (∨ᵗ-l nf ng) u ⟩
  nf ∨ᵗ ng , (n , λ b → weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b)))
    ≈⟨ ≈lstage (nf ∨ᵗ ng) (≈node c') ⟩
  nf ∨ᵗ ng , (n , λ b → weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)))
    ≈⟨ ≈lsym (≈lstep (∨ᵗ-r nf ng) (n , (λ b → weaken (g1 b) ng _ (g2 b)))) ⟩
  ng , (n , λ b → weaken (g1 b) ng (fi≤sup n g1 b) (g2 b)) ∎
  where
  open Diagram D
  f1 : B → BTree
  f1 b = f b .proj₁
  f2 : ∀ b → P₀ (f1 b)
  f2 b = f b .proj₂
  nf : BTree
  nf = sup (n , f1)
  g1 : B → BTree
  g1 b = g b .proj₁
  g2 : ∀ b → P₀ (g1 b)
  g2 b = g b .proj₂
  ng : BTree
  ng = sup (n , g1)
  d : ∀ b → Colim D [ f b ≈ g b ] → f2 b ≈ᴾ g2 b
  d b = recˡ D (λ {s} {t} p → s .proj₂ ≈ᴾ t .proj₂)
             (λ i e → e)
             ≈pweaken
             (λ _ → ≈psym)
             (λ _ _ → ≈ptrans)
  c' : ∀ b → P (nf ∨ᵗ ng) [ weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b))
                          ≈ weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)) ]
  c' b = begin
    weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b)) 
      ≈⟨ ≈psym (≈pweaken (∨ᵗ-l nf ng) (weaken (f1 b) nf _ (f2 b))) ⟩
    weaken (f1 b) nf _ (f2 b) 
      ≈⟨ ≈psym (≈pweaken (fi≤sup n f1 b) (f2 b)) ⟩
    f2 b
      ≈⟨ d b (c b) ⟩
    g2 b
      ≈⟨ ≈pweaken (fi≤sup n g1 b) (g2 b) ⟩
    weaken (g1 b) ng _ (g2 b)
      ≈⟨ ≈pweaken (∨ᵗ-r nf ng) (weaken (g1 b) ng _ (g2 b)) ⟩
    weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)) ∎
    where
    import QIT.Setoid.Indexed as Indexed
    open Indexed.≈syntax Pᴵ
  open ≈.Hom
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}
  u : ⟨ Diagram.D-ob (F̃ ∘ D) nf ⟩
  u = n , (λ b → weaken (f1 b) nf _ (f2 b))
ψ-cong (≈perm {f} π) = u
  where
  π' : B → B
  π' = π .↔.to
  g : B → P₀ (sup (n , (λ b → f b .proj₁)))
  g b = weaken (f b .proj₁) (sup (n , (λ b → f b .proj₁)))
               (fi≤sup n _ b) (f b .proj₂)
  h : B → P₀ (sup (n , (λ b → f (π' b) .proj₁)))
  h b = weaken (f (π' b) .proj₁) (sup (n , (λ b → f (π' b) .proj₁)))
                (fi≤sup n _ b) (f (π' b) .proj₂)
  g' : B → P₀ (sup (n , (λ b → f b .proj₁)))
  g' b = weaken (f (π' b) .proj₁) (sup (n , (λ b → f b .proj₁)))
                (fi≤sup n _ (π' b)) (f (π' b) .proj₂)
  le : sup (n , λ b → f b .proj₁) ≤ sup (n , λ b → f (π' b) .proj₁)
  le = sup≤ λ b → <sup (π .↔.from b)
    (substp (λ ○ → f b .proj₁ ≤ f ○ .proj₁) (≡.sym (↔.linv π b)) (≤refl (f b .proj₁)))
  u : Colim (F̃ ∘ D)
    [ sup (n , λ b → f b .proj₁) , (n , g)
    ≈ sup (n , λ b → f (π' b) .proj₁) , (n , h) ]
  u = begin
    sup (n , (λ b → f b .proj₁)) , (n , g)
      ≈⟨ ≈lstage (sup (n , (λ b → f b .proj₁))) (≈perm π) ⟩
    sup (n , (λ b → f b .proj₁)) , (n , g')
      ≈⟨ ≈lstep le (n , g') ⟩
    sup (n , (λ b → f (π' b) .proj₁)) , (n , λ b → weaken _ _ le (g' b))
      ≈⟨ ≈lstage _ (≈node v) ⟩
    sup (n , (λ b → f (π' b) .proj₁)) , (n , h) ∎
    where
    v : ∀ b → weaken _ _ le (g' b) ≈ᴾ h b
    v b = begin
      weaken _ _ le (g' b)
        ≈⟨ ≈psym (≈pweaken le (g' b)) ⟩
      g' b
        ≈⟨ ≈psym (≈pweaken (fi≤sup n (λ b₃ → f b₃ .proj₁) (π' b)) (f (π' b) .proj₂)) ⟩
      f (π' b) .proj₂
        ≈⟨ (≈pweaken (fi≤sup n (λ b₃ → f (π' b₃) .proj₁) b) (f (π' b) .proj₂)) ⟩
      h b ∎
      where
      import QIT.Setoid.Indexed as Indexed
      open Indexed.≈syntax Pᴵ
    open Setoid (Colim (F̃ ∘ D))
    open ≈.≈syntax {S = Colim (F̃ ∘ D)}
  open ≈.Hom
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}
ψ-cong (≈trans p q) = ≈ltrans (ψ-cong p) (ψ-cong q)

linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
linv (l , f) = begin
  ϕ₀ (ψ₀ (l , f))
    ≈⟨ refl ⟩
  (l , λ ())
    ≈⟨ ≈leaf ⟩
  (l , f) ∎
  where
    open ≈.≈syntax {S = (F.F-ob (Colim D))}
    open Setoid (F.F-ob (Colim D))
linv (n , g) =
  ϕ₀ (ψ₀ (n , g))
    ≈⟨ refl ⟩
  (n , λ b → t* , weaken (t b) t* _ (f b))
    ≈⟨ ≈node (λ b → ≈lsym (≈lstep (fi≤sup n t b) (f b))) ⟩
  (n , λ b → t b , f b)
    ≈⟨ refl ⟩
  (n , g) ∎
  where
  open Setoid (F.F-ob (Colim D))
  open Diagram D
  t : B → BTree
  t b = g b .proj₁
  f : ∀ b → P₀ (t b)
  f b = g b .proj₂
  t* : BTree
  t* = sup (n , t) 
  --   open ≈.Hom
  open ≈.≈syntax {S = (F.F-ob (Colim D))}

rinv : ∀ x → Colim (F̃ ∘ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
rinv (i , (l , f)) = begin
  ψ₀ (ϕ₀ (i , (l , f)))
    ≈⟨ refl ⟩
  ψ₀ (l , g)
    ≈⟨ ≈lstage 𝟘 ≈leaf ⟩
  𝟘 , (l , h)
    ≈⟨ ≈lstep (𝟘≤t i) (l , h) ⟩
  i , (l , λ b → weaken 𝟘 i (𝟘≤t i) (h b))
    ≈⟨ ≡→≈ (Colim (F̃ ∘ D)) (≡.cong (λ ○ → i , (l , ○)) (funExt (λ ()))) ⟩
  i , (l , f) ∎
  where
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}
  g : ⊥* → ⟨ Colim D ⟩
  g ()
  h : ⊥* → ⟨ D.D-ob 𝟘 ⟩
  h ()
rinv (i , (n , g)) = begin
  ψ₀ (ϕ₀ (i , (n , g)))
    ≈⟨ refl ⟩
  ψ₀ (n , (λ b → i , g b))
    ≈⟨ refl ⟩
  suc i , n , (λ b → weaken i (suc i) (<→≤ (<suc i)) (g b))
    ≈⟨ ≈lsym (≈lstep (<→≤ (<suc i)) (n , g)) ⟩
  i , (n , g) ∎
  where
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}

cocontinuous : Cocontinuous F̃ D
cocontinuous = ∣ iso ∣
  where
  iso : ≈.Iso (Colim (F̃ ∘ D)) (F.F-ob (Colim D))
  iso = record
    { ⟦_⟧ = ϕ₀
    ; ⟦_⟧⁻¹ = ψ₀
    ; cong = ϕ-cong
    ; cong⁻¹ = ψ-cong
    ; linv = linv
    ; rinv = rinv
    }

