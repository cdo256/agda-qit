open import QIT.Prelude

module QIT.Mobile.Cocontinuity
  (I : Set) (inhabI : ∥ I ∥) where

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Mobile.Base I
open import QIT.Mobile.Diagram I inhabI
open import QIT.Setoid as ≈
open import Data.Product
open import Data.Empty renaming (⊥-elim to absurd)
open import QIT.Container
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import QIT.Relation.Plump Sᵀ Pᵀ

open import QIT.Diagram ≤p hiding (_≤_)
open import QIT.Colimit ≤p ℓ0 ℓ0
open import QIT.Cocontinuity ≤p
open import QIT.Mobile.Functor I

module F = ≈.Functor F̃
module D = Diagram D
module F∘D = Diagram (F̃ ∘ D)

private
  L = Colim (F̃ ∘ D)
  R = F.F-ob (Colim D)

ϕ₀ : ⟨ Colim (F̃ ∘ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (i , (l , _)) = l , (λ ())
ϕ₀ (i , (n , f)) = n , (λ b → i , f b)

mutual
  ϕ-cong : ∀ {x y} → Colim (F̃ ∘ D) [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
  ϕ-cong (≈lstage i e) = ϕ-cong-inner i e
  ϕ-cong (≈lstep {i} {j} p (l , _)) = ≈leaf
  ϕ-cong (≈lstep {i} {j} (sup≤ p) (n , f)) = ≈node λ b → ≈lstep (sup≤ p) (f b)
  ϕ-cong (≈lsym p) = ≈sym (Colim D) (ϕ-cong p)
  ϕ-cong (≈ltrans p q) = ≈trans (ϕ-cong p) (ϕ-cong q)

  ϕ-cong-inner : ∀ i {x y} → F∘D.D-ob i [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ (i , x) ≈ ϕ₀ (i , y) ]
  ϕ-cong-inner i ≈leaf = ≈leaf
  ϕ-cong-inner i (≈node c) = ≈node λ b → ≈lstage i (c b)
  ϕ-cong-inner i (≈perm π) = ≈perm π
  ϕ-cong-inner i (≈trans p q) = ≈trans (ϕ-cong-inner i p) (ϕ-cong-inner i q)


ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F̃ ∘ D) ⟩
ψ₀ (l , _) = ⊥ᶻ , l , λ()
ψ₀ (n , f) = α , n , g
  where
  μ : I → Z
  μ i = f i .proj₁
  α : Z
  α = sup (ιˢ n , μ)
  h : (i : I) → P₀ (μ i)
  h i = f i .proj₂
  g : I → P₀ α
  g i = pweaken (fi≤sup (ιˢ n) μ i) (h i)

ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ] → Colim (F̃ ∘ D) [ ψ₀ x ≈ ψ₀ y ]
-- ψ-cong ≈leaf = ≈lstage ⊥ᶻ ≈leaf
-- ψ-cong (≈node {f} {g} c) = begin
--   nf , n , (λ i → pweaken (sup≤ (λ x → <sup x (f x .proj₂ .snd))) {!!})
--     ≈⟨ {!!} ⟩
--   ng , {!!} ∎
--   where
--   nf : Z
--   nf = sup (ιˢ n , λ i → f i .proj₁)
--   ng : Z
--   ng = sup (ιˢ n , λ i → g i .proj₁)
--   open ≈.Hom
--   open Setoid (Colim (F̃ ∘ D))
--   open ≈.≈syntax {S = Colim (F̃ ∘ D)}

ψ-cong {x} {y} (≈perm π) = {!!}
ψ-cong {x} {y} (≈trans x≈y x≈y₁) = {!!}

-- ψ-cong ≈leaf = ≈lstage 𝟘 ≈leaf
-- ψ-cong (≈node {f} {g} c) = {!begin
--   nf , (n , λ b → weaken (f1 b) nf (fi≤sup n f1 b) (f2 b))
--     ≈⟨ ≈lstep (∨ᵗ-l nf ng) u ⟩
--   nf ∨ᵗ ng , (n , λ b → weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b)))
--     ≈⟨ ≈lstage (nf ∨ᵗ ng) (≈node c') ⟩
--   nf ∨ᵗ ng , (n , λ b → weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)))
--     ≈⟨ ≈lsym (≈lstep (∨ᵗ-r nf ng) (n , (λ b → weaken (g1 b) ng _ (g2 b)))) ⟩
--   ng , (n , λ b → weaken (g1 b) ng (fi≤sup n g1 b) (g2 b)) ∎!}
ψ-cong (≈node {f} {g} c) = begin
  α1 , n , h1
    ≈⟨ ≈lstep {!!} (n , h1) ⟩
  {!!} , n , {!!}
    ≈⟨ {!!} ⟩
  α2 , n , h2 ∎
  where
  open Diagram D
  f1 : I → Z
  f1 i = f i .proj₁
  g1 : ∀ i → P₀ (f1 i)
  g1 i = f i .proj₂
  α1 : Z
  α1 = sup (ιˢ n , f1)
  h1 : I → P₀ α1
  h1 i = pweaken (fi≤sup (ιˢ n) f1 i) (g1 i)
  f2 : I → Z
  f2 i = g i .proj₁
  g2 : ∀ i → P₀ (f2 i)
  g2 i = g i .proj₂
  α2 : Z
  α2 = sup (ιˢ n , f2)
  h2 : I → P₀ α2
  h2 i = pweaken (fi≤sup (ιˢ n) f2 i) (g2 i)
  t1 : T
  t1 = sup (n , (λ i → g1 i .fst))
  t2 : T
  t2 = sup (n , (λ i → g1 i .fst))
  d : ∀ {s t} → Colim D [ s ≈ t ] → (s .proj₂ .fst) ≈ᴾᴵ (t .proj₂ .fst)
  d r = recˡ D C c-stage c-step c-sym c-trans r
    where
    C : ∀ {s t} → Colim D [ s ≈ t ] → Prop
    C {_ , s , _} {_ , t , _} p = s  ≈ᴾᴵ t
    c-stage : ∀ α {x x'} (e : P α [ x ≈ x' ]) → C (≈lstage α e)
    c-stage α {x} {x'} e = mkPI α (x .snd) (x' .snd) e
    c-step : ∀ {α β} (p : α ≤ β) (x : ⟨ P α ⟩) → C (≈lstep p x)
    c-step {α} {β} α≤β (s , s≤α) = mkPI β (≤≤ α≤β s≤α) (≤≤ α≤β s≤α) ≈prefl
    c-sym : ∀ {s t} (r : Colim D [ s ≈ t ]) → C r → C (≈lsym r)
    c-sym _ p = ≈pisym p
    c-trans : ∀ {s t u} (r₁ : Colim D [ s ≈ t ]) (r₂ : Colim D [ t ≈ u ]) → C r₁ → C r₂ → C (≈ltrans r₁ r₂)
    c-trans _ _ p q = ≈pitrans p q
  β : t1 ≈ᴾᴵ t2 → Colim (F̃ ∘ D) [ α1 , n , h1 ≈ α2 , n , h2 ]
  β (mkPI α s≤α t≤α e) = begin
    α1 , n , h1
      ≈⟨ ≈lstep (≤≤ ∨ᶻ-r ∨ᶻ-l) (n , h1) ⟩
    α ∨ᶻ (α1 ∨ᶻ α2) , n , (λ b → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-l) (h1 b))
      ≈⟨ ≈lstage _ u ⟩
    α ∨ᶻ (α1 ∨ᶻ α2) , n , (λ b → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-r) (h2 b))
      ≈⟨ ≈lsym (≈lstep (≤≤ ∨ᶻ-r ∨ᶻ-r) (n , h2)) ⟩
    α2 , n , h2 ∎
    where
    v : ∀ i → Colim D [ f i ≈ g i ]
      → (α ∨ᶻ (α1 ∨ᶻ α2)) ⊢  pweaken (≤≤ (≤≤ ∨ᶻ-r ∨ᶻ-l) (fi≤sup _ f1 i)) (f i .proj₂)
                          ≈ᴾ pweaken (≤≤ (≤≤ ∨ᶻ-r ∨ᶻ-r) (fi≤sup _ f2 i)) (g i .proj₂)
    v i = recˡ D {!!} {!!} {!!} {!!} {!!}
      where
      C : ∀ {s t} (p : Colim D [ s ≈ t ]) → {!α ∨ᶻ (α1 ∨ᶻ α2) ⊢ ? ≈ᴾ ?!}
    u : F∘D.D-ob (α ∨ᶻ (α1 ∨ᶻ α2)) [
         n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-l) (h1 i)) ≈
         n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-r) (h2 i)) ]
    u = begin
      n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-l) (pweaken (fi≤sup _ f1 i) (f i .proj₂)))
        ≈⟨ ≈node (λ i → v i (c i)) ⟩
      n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-r) (pweaken (fi≤sup _ f2 i) (g i .proj₂))) ∎
      where
      open Setoid (F∘D.D-ob (α ∨ᶻ (α1 ∨ᶻ α2)))
      open ≈.≈syntax {S = F∘D.D-ob (α ∨ᶻ (α1 ∨ᶻ α2))}
    open ≈.Hom
    open Setoid (Colim (F̃ ∘ D))
    open ≈.≈syntax {S = Colim (F̃ ∘ D)}
    
--   c' : ∀ b → P (nf ∨ᵗ ng) [ weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b))
--                           ≈ weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)) ]
--   c' b = begin
--     weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b))
--       ≈⟨ ≈psym (≈pweaken (∨ᵗ-l nf ng) (weaken (f1 b) nf _ (f2 b))) ⟩
--     weaken (f1 b) nf _ (f2 b)
--       ≈⟨ ≈psym (≈pweaken (fi≤sup n f1 b) (f2 b)) ⟩
--     f2 b
--       ≈⟨ d b (c b) ⟩
--     g2 b
--       ≈⟨ ≈pweaken (fi≤sup n g1 b) (g2 b) ⟩
--     weaken (g1 b) ng _ (g2 b)
--       ≈⟨ ≈pweaken (∨ᵗ-r nf ng) (weaken (g1 b) ng _ (g2 b)) ⟩
--     weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)) ∎
--     where
--     import QIT.Setoid.Indexed as Indexed
--     open Indexed.≈syntax Pᴵ
  open ≈.Hom
  open Setoid (Colim (F̃ ∘ D))
  open ≈.≈syntax {S = Colim (F̃ ∘ D)}
--   u : ⟨ F∘D.D-ob nf ⟩
--   u = n , (λ b → weaken (f1 b) nf _ (f2 b))
-- -- ψ-cong (≈perm {f} π) = u
-- --   where
-- --   π' : I → I
-- --   π' = π .↔.to
-- --   g : I → P₀ (sup (n , (λ b → f b .proj₁)))
-- --   g b = weaken (f b .proj₁) (sup (n , (λ b → f b .proj₁)))
-- --                (fi≤sup n _ b) (f b .proj₂)
-- --   h : I → P₀ (sup (n , (λ b → f (π' b) .proj₁)))
-- --   h b = weaken (f (π' b) .proj₁) (sup (n , (λ b → f (π' b) .proj₁)))
-- --                 (fi≤sup n _ b) (f (π' b) .proj₂)
-- --   g' : I → P₀ (sup (n , (λ b → f b .proj₁)))
-- --   g' b = weaken (f (π' b) .proj₁) (sup (n , (λ b → f b .proj₁)))
-- --                 (fi≤sup n _ (π' b)) (f (π' b) .proj₂)
-- --   le : sup (n , λ b → f b .proj₁) ≤ sup (n , λ b → f (π' b) .proj₁)
-- --   le = sup≤ λ b → <sup (π .↔.from b)
-- --     (substp (λ ○ → f b .proj₁ ≤ f ○ .proj₁) (≡.sym (↔.linv π b)) (≤refl (f b .proj₁)))
-- --   u : Colim (F̃ ∘ D)
-- --     [ sup (n , λ b → f b .proj₁) , (n , g)
-- --     ≈ sup (n , λ b → f (π' b) .proj₁) , (n , h) ]
-- --   u = begin
-- --     sup (n , (λ b → f b .proj₁)) , (n , g)
-- --       ≈⟨ ≈lstage (sup (n , (λ b → f b .proj₁))) (≈perm π) ⟩
-- --     sup (n , (λ b → f b .proj₁)) , (n , g')
-- --       ≈⟨ ≈lstep le (n , g') ⟩
-- --     sup (n , (λ b → f (π' b) .proj₁)) , (n , λ b → weaken _ _ le (g' b))
-- --       ≈⟨ ≈lstage _ (≈node v) ⟩
-- --     sup (n , (λ b → f (π' b) .proj₁)) , (n , h) ∎
-- --     where
-- --     v : ∀ b → weaken _ _ le (g' b) ≈ᴾ h b
-- --     v b = begin
-- --       weaken _ _ le (g' b)
-- --         ≈⟨ ≈psym (≈pweaken le (g' b)) ⟩
-- --       g' b
-- --         ≈⟨ ≈psym (≈pweaken (fi≤sup n (λ b₃ → f b₃ .proj₁) (π' b)) (f (π' b) .proj₂)) ⟩
-- --       f (π' b) .proj₂
-- --         ≈⟨ (≈pweaken (fi≤sup n (λ b₃ → f (π' b₃) .proj₁) b) (f (π' b) .proj₂)) ⟩
-- --       h b ∎
-- --       where
-- --       import QIT.Setoid.Indexed as Indexed
-- --       open Indexed.≈syntax Pᴵ
-- --     open Setoid (Colim (F̃ ∘ D))
-- --     open ≈.≈syntax {S = Colim (F̃ ∘ D)}
-- --   open ≈.Hom
-- --   open Setoid (Colim (F̃ ∘ D))
-- --   open ≈.≈syntax {S = Colim (F̃ ∘ D)}
-- -- ψ-cong (≈trans p q) = ≈ltrans (ψ-cong p) (ψ-cong q)

-- -- linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
-- -- linv (l , f) = begin
-- --   ϕ₀ (ψ₀ (l , f))
-- --     ≈⟨ refl ⟩
-- --   (l , λ ())
-- --     ≈⟨ ≈leaf ⟩
-- --   (l , f) ∎
-- --   where
-- --     open ≈.≈syntax {S = (F.F-ob (Colim D))}
-- --     open Setoid (F.F-ob (Colim D))
-- -- linv (n , g) =
-- --   ϕ₀ (ψ₀ (n , g))
-- --     ≈⟨ refl ⟩
-- --   (n , λ b → t* , weaken (t b) t* _ (f b))
-- --     ≈⟨ ≈node (λ b → ≈lsym (≈lstep (fi≤sup n t b) (f b))) ⟩
-- --   (n , λ b → t b , f b)
-- --     ≈⟨ refl ⟩
-- --   (n , g) ∎
-- --   where
-- --   open Setoid (F.F-ob (Colim D))
-- --   open Diagram D
-- --   t : I → BTree
-- --   t b = g b .proj₁
-- --   f : ∀ b → P₀ (t b)
-- --   f b = g b .proj₂
-- --   t* : BTree
-- --   t* = sup (n , t)
-- --   --   open ≈.Hom
-- --   open ≈.≈syntax {S = (F.F-ob (Colim D))}

-- -- rinv : ∀ x → Colim (F̃ ∘ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
-- -- rinv (i , (l , f)) = begin
-- --   ψ₀ (ϕ₀ (i , (l , f)))
-- --     ≈⟨ refl ⟩
-- --   ψ₀ (l , g)
-- --     ≈⟨ ≈lstage 𝟘 ≈leaf ⟩
-- --   𝟘 , (l , h)
-- --     ≈⟨ ≈lstep (𝟘≤t i) (l , h) ⟩
-- --   i , (l , λ b → weaken 𝟘 i (𝟘≤t i) (h b))
-- --     ≈⟨ ≡→≈ (Colim (F̃ ∘ D)) (≡.cong (λ ○ → i , (l , ○)) (funExt (λ ()))) ⟩
-- --   i , (l , f) ∎
-- --   where
-- --   open Setoid (Colim (F̃ ∘ D))
-- --   open ≈.≈syntax {S = Colim (F̃ ∘ D)}
-- --   g : ⊥* → ⟨ Colim D ⟩
-- --   g ()
-- --   h : ⊥* → ⟨ D.D-ob 𝟘 ⟩
-- --   h ()
-- -- rinv (i , (n , g)) = begin
-- --   ψ₀ (ϕ₀ (i , (n , g)))
-- --     ≈⟨ refl ⟩
-- --   ψ₀ (n , (λ b → i , g b))
-- --     ≈⟨ refl ⟩
-- --   suc i , n , (λ b → weaken i (suc i) (<→≤ (<suc i)) (g b))
-- --     ≈⟨ ≈lsym (≈lstep (<→≤ (<suc i)) (n , g)) ⟩
-- --   i , (n , g) ∎
-- --   where
-- --   open Setoid (Colim (F̃ ∘ D))
-- --   open ≈.≈syntax {S = Colim (F̃ ∘ D)}

-- -- cocontinuous : Cocontinuous F̃ D
-- -- cocontinuous = ∣ iso ∣
-- --   where
-- --   iso : ≈.Iso (Colim (F̃ ∘ D)) (F.F-ob (Colim D))
-- --   iso = record
-- --     { ⟦_⟧ = ϕ₀
-- --     ; ⟦_⟧⁻¹ = ψ₀
-- --     ; cong = ϕ-cong
-- --     ; cong⁻¹ = ψ-cong
-- --     ; linv = linv
-- --     ; rinv = rinv
-- --     }
